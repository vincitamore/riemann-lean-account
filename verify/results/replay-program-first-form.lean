/-
A full kernel replay of everything `Main` imports, into an environment that starts empty.

What it does. It imports `Main` once, takes every constant of every module in the import
closure (the archive, Mathlib and its dependencies, and Lean's own library), puts them in a
dependency order, and passes each declaration to the Lean kernel (`Kernel.Environment.addDeclCore`)
against an environment that contains only declarations earlier in that order. Constructors and
recursors are not sent; as in Lean's own `Lean.Environment.replay`, they are compared at the end
with the ones the kernel generated from the inductive declarations.

How it differs from the toolchain's `leanchecker`, and why.
* `leanchecker` re-imports the whole import closure once per module. On this archive (175,187
  modules, nearly every one importing nearly all of the others) that is quadratic; its first
  batch exceeded the machine's memory limit.
* `leanchecker --fresh` replays in one process, but orders the declarations with
  `Expr.getUsedConstants`, which keeps only a small cache of visited subterms and does not
  terminate in practical time on some of this archive's proof terms; and it checks on one thread.
* Here the order is computed with a traversal that remembers every visited node, and the checks
  run in parallel. For a definition, theorem, opaque constant or axiom, the kernel check runs in
  a task against a snapshot of the environment, while the main thread adds the same declaration
  with `addDeclWithoutChecking` and moves on. Each declaration is therefore checked by the kernel
  against exactly the declarations before it, which is what a sequential replay does; only the
  schedule differs. Inductive types are added, checked, on the main thread.
The run ends with a self-test: the same check must accept `True.intro : True` and reject
`True.intro : False`.

Build (in this directory):   lake build replay
Run (from the archive root, so that LEAN_PATH points at the built archive):
    lake env /path/to/replay/.lake/build/bin/replay <output-directory>
Outputs: replay-summary.txt, replay-failures.txt, replay-axioms.txt, replay-skipped.txt.
-/
import Lean
open Lean

/-- The constants occurring in an expression, with every visited node remembered (by address),
so the cost is linear in the size of the term as a graph. -/
unsafe def usedConstsImpl (e : Expr) : Array Name := Id.run do
  let mut visited : Std.HashSet USize := {}
  let mut out : Std.HashSet Name := {}
  let mut stack : Array Expr := #[e]
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    match x with
    | .const n _ => out := out.insert n
    -- the kernel unfolds literals into these constants, so they must come first
    | .lit (.natVal _) => out := ((out.insert `Nat).insert `Nat.zero).insert `Nat.succ
    | .lit (.strVal _) =>
      for c in [`String, `String.ofList, `String.mk, `Char, `Char.ofNat, `List.cons, `List.nil] do
        out := out.insert c
    | .bvar _ | .fvar _ | .mvar _ | .sort _ => pure ()
    | _ =>
      let addr := ptrAddrUnsafe x
      if visited.contains addr then continue
      visited := visited.insert addr
      match x with
      | .app f a => stack := (stack.push f).push a
      | .lam _ t b _ => stack := (stack.push t).push b
      | .forallE _ t b _ => stack := (stack.push t).push b
      | .letE _ t v b _ => stack := ((stack.push t).push v).push b
      | .mdata _ b => stack := stack.push b
      | .proj s _ b => out := out.insert s; stack := stack.push b
      | _ => pure ()
  return out.toArray

@[implemented_by usedConstsImpl]
opaque usedConsts (e : Expr) : Array Name

def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- What a declaration must wait for. For an inductive type this is everything its whole
mutual block and all of its constructors mention. -/
def depsOf (all : Std.HashMap Name ConstantInfo) (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := usedConsts ci.type
  match ci with
  | .defnInfo v => out := out ++ usedConsts v.value
  | .thmInfo v => out := out ++ usedConsts v.value
  | .opaqueInfo v => out := out ++ usedConsts v.value
  | .inductInfo v =>
    for o in v.all do
      match all[o]? with
      | some (.inductInfo w) =>
        out := out ++ usedConsts w.type
        for c in w.ctors do
          match all[c]? with
          | some cc => out := out ++ usedConsts cc.type
          | none => pure ()
      | _ => pure ()
  | .quotInfo _ => out := out.push `Eq
  | _ => pure ()
  return out

abbrev Check := Task (Option Kernel.Exception)

/-- The kernel check of one declaration against a snapshot. `none` means accepted. -/
-- The check is the body of a pure task. (Written as an `IO` action built from a `match` on the
-- result, the check would run when the action is built, on the calling thread.)
def spawnCheck (snap : Kernel.Environment) (d : Declaration) : Check :=
  Task.spawn fun _ =>
    match snap.addDeclCore 0 0 d (cancelTk? := none) with
    | .ok _ => none
    | .error ex => some ex

structure St where
  kenv : Kernel.Environment
  pending : Array (Name × Check) := #[]
  failures : Array (Name × String) := #[]
  postCtor : Array Name := #[]
  postRec : Array Name := #[]
  axioms : Array Name := #[]
  quotDone : Bool := false
  nThm : Nat := 0
  nDef : Nat := 0
  nOpq : Nat := 0
  nAx : Nat := 0
  nBlocks : Nat := 0
  nInd : Nat := 0
  emitted : Nat := 0
  nAlt : Nat := 0
  nAltDiff : Nat := 0

abbrev M := StateRefT St IO

def fail (n : Name) (msg : String) : M Unit := do
  modify fun s => { s with failures := s.failures.push (n, msg) }
  say s!"FAIL {n}: {(msg.take 400).replace "\n" " "}"

def drain : M Unit := do
  let ps := (← get).pending
  modify fun s => { s with pending := #[] }
  for (n, t) in ps do
    match (← IO.wait t) with
    | none => pure ()
    | some ex => fail n (← (ex.toMessageData {}).toString)

/-- Check in a task, add unchecked on this thread. -/
def checkedLater (n : Name) (d : Declaration) (window : Nat) : M Unit := do
  let snap := (← get).kenv
  let t := spawnCheck snap d
  modify fun s => { s with pending := s.pending.push (n, t) }
  match snap.addDeclWithoutChecking d with
  | .ok e => modify fun s => { s with kenv := e }
  | .error ex => fail n s!"could not be added: {← (ex.toMessageData {}).toString}"
  if (← get).pending.size ≥ window then drain

def checkedNow (n : Name) (d : Declaration) : M Unit := do
  match (← get).kenv.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok e => modify fun s => { s with kenv := e }
  | .error ex => fail n (← (ex.toMessageData {}).toString)

def emit (all : Std.HashMap Name ConstantInfo) (alts : Std.HashMap Name (Array ConstantInfo))
    (n : Name) (window : Nat) : M Unit := do
  let some ci := all[n]? | return
  modify fun s => { s with emitted := s.emitted + 1 }
  -- A name that two modules both declare (private declarations under the module system): the
  -- last version is the one added, and every other version is checked as well.
  for alt in alts.getD n #[] do
    let d? : Option Declaration := match alt with
      | .defnInfo i => some (.defnDecl i)
      | .thmInfo i => some (.thmDecl i)
      | .opaqueInfo i => some (.opaqueDecl i)
      | _ => none
    if let some d := d? then
      let t := spawnCheck (← get).kenv d
      modify fun s => { s with pending := s.pending.push (n, t), nAlt := s.nAlt + 1,
                               nAltDiff := if alt.type == ci.type then s.nAltDiff else s.nAltDiff + 1 }
  match ci with
  | .defnInfo info =>
    modify fun s => { s with nDef := s.nDef + 1 }
    checkedLater n (.defnDecl info) window
  | .thmInfo info =>
    modify fun s => { s with nThm := s.nThm + 1 }
    checkedLater n (.thmDecl info) window
  | .opaqueInfo info =>
    modify fun s => { s with nOpq := s.nOpq + 1 }
    checkedLater n (.opaqueDecl info) window
  | .axiomInfo info =>
    modify fun s => { s with nAx := s.nAx + 1, axioms := s.axioms.push n }
    checkedLater n (.axiomDecl info) window
  | .inductInfo info =>
    -- a mutual block is added once, when its first member is reached
    if ((← get).kenv.find? n).isSome then return
    let mut types : List InductiveType := []
    for o in info.all.reverse do
      match all[o]? with
      | some (.inductInfo w) =>
        let ctors := w.ctors.filterMap fun c =>
          (all[c]?).map fun cc => ({ name := cc.name, type := cc.type } : Constructor)
        types := { name := w.name, type := w.type, ctors := ctors } :: types
      | _ => fail n s!"member {o} of the mutual block is missing"
    modify fun s => { s with nBlocks := s.nBlocks + 1, nInd := s.nInd + info.all.length }
    checkedNow n (.inductDecl info.levelParams info.numParams types false)
  | .ctorInfo _ => modify fun s => { s with postCtor := s.postCtor.push n }
  | .recInfo _ => modify fun s => { s with postRec := s.postRec.push n }
  | .quotInfo _ =>
    unless (← get).quotDone do
      modify fun s => { s with quotDone := true }
      checkedNow n .quotDecl

unsafe def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "."
  -- the module whose import closure is replayed; `Main` unless a second argument names another
  let root := (args.getD 1 "Main").toName
  let window := ((← IO.getEnv "REPLAY_WINDOW").bind String.toNat?).getD 20000
  initSearchPath (← findSysroot)
  let t0 ← IO.monoMsNow
  say s!"importing {root}"
  let env ← importModules #[{ module := root }] {} (trustLevel := 1024)
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut all : Std.HashMap Name ConstantInfo := {}
  let mut order : Array Name := #[]
  let mut skipped : Array Name := #[]
  let mut alts : Std.HashMap Name (Array ConstantInfo) := {}
  let mut dup := 0
  for i in [0:mods.size] do
    let md := data[i]!
    for j in [0:md.constNames.size] do
      let n := md.constNames[j]!
      let ci := md.constants[j]!
      match all[n]? with
      | some prev =>
        dup := dup + 1
        alts := alts.insert n ((alts.getD n #[]).push prev)
      | none => if ci.isUnsafe || ci.isPartial then skipped := skipped.push n else order := order.push n
      all := all.insert n ci
  let depsFor (n : Name) (ci : ConstantInfo) : Array Name :=
    (alts.getD n #[]).foldl (fun acc a => acc ++ depsOf all a) (depsOf all ci)
  say s!"modules {mods.size}, constants {all.size}, to replay {order.size}, unsafe or partial (not replayed) {skipped.size}, duplicate names {dup}, {((← IO.monoMsNow) - t0) / 1000} s"
  let fresh ← mkEmptyEnvironment
  let init : St := { kenv := fresh.toKernelEnv }
  let (_, st) ← (do
    -- 0 = not reached, 1 = on the stack, 2 = done
    let mut status : Std.HashMap Name UInt8 := {}
    for n in skipped do status := status.insert n 2
    let mut stack : Array (Name × Array Name × Nat) := #[]
    for root in order do
      if (status.getD root 0) != 0 then continue
      status := status.insert root 1
      stack := stack.push (root, depsFor root (all[root]!), 0)
      while !stack.isEmpty do
        let (n, ds, i) := stack.back!
        if i < ds.size then
          stack := stack.modify (stack.size - 1) fun (a, b, _) => (a, b, i + 1)
          let d := ds[i]!
          if (status.getD d 0) == 0 then
            match all[d]? with
            | some ci =>
              status := status.insert d 1
              stack := stack.push (d, depsFor d ci, 0)
            | none => pure ()
        else
          stack := stack.pop
          status := status.insert n 2
          emit all alts n window
          let e := (← get).emitted
          if e % 100000 == 0 then
            say s!"  {e} of {order.size} declarations sent, {(← get).failures.size} failed, {((← IO.monoMsNow) - t0) / 1000} s"
    drain
    say s!"all declarations checked, {((← IO.monoMsNow) - t0) / 1000} s; comparing constructors and recursors"
    -- constructors and recursors must equal the ones the kernel generated
    for c in (← get).postCtor do
      match (← get).kenv.find? c, all[c]? with
      | some (.ctorInfo a), some (.ctorInfo b) => unless a == b do fail c "constructor differs from the generated one"
      | _, _ => fail c "no such constructor was generated"
    for r in (← get).postRec do
      match (← get).kenv.find? r, all[r]? with
      | some (.recInfo a), some (.recInfo b) => unless a == b do fail r "recursor differs from the generated one"
      | _, _ => fail r "no such recursor was generated"
    : M Unit).run init
  -- self-test of the check itself, against the final environment
  let good : Declaration := .thmDecl { name := `_replay_selftest_true, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  let bad : Declaration := .thmDecl { name := `_replay_selftest_false, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  let rGood ← IO.wait (spawnCheck st.kenv good)
  let rBad ← IO.wait (spawnCheck st.kenv bad)
  let okGood := rGood.isNone
  let okBad := rBad.isSome
  let secs := ((← IO.monoMsNow) - t0) / 1000
  let mut out := s!"REPLAY-SUMMARY\nmodules {mods.size}\nconstants {all.size}\nreplayed {order.size}\n"
  out := out ++ s!"theorems {st.nThm}\ndefinitions {st.nDef}\nopaque {st.nOpq}\naxioms {st.nAx}\n"
  out := out ++ s!"inductive-types {st.nInd} in {st.nBlocks} blocks\nconstructors-compared {st.postCtor.size}\nrecursors-compared {st.postRec.size}\n"
  out := out ++ s!"unsafe-or-partial-not-replayed {skipped.size}\nfailed {st.failures.size}\n"
  out := out ++ s!"names-declared-more-than-once {dup}, other versions also checked {st.nAlt}, of which with a different type {st.nAltDiff}\n"
  out := out ++ s!"selftest accepts-true {okGood} rejects-false {okBad}\nseconds {secs}\n"
  IO.FS.writeFile (outDir ++ "/replay-summary.txt") out
  IO.FS.writeFile (outDir ++ "/replay-failures.txt")
    (String.intercalate "\n" (st.failures.toList.map fun (n, m) => s!"{n}\t{m.replace "\n" " "}"))
  IO.FS.writeFile (outDir ++ "/replay-axioms.txt") (String.intercalate "\n" (st.axioms.toList.map toString))
  IO.FS.writeFile (outDir ++ "/replay-skipped.txt") (String.intercalate "\n" (skipped.toList.map toString))
  say out
  say s!"REPLAY-DONE failed={st.failures.size} selftest={okGood && okBad}"
  return (if st.failures.isEmpty && okGood && okBad then 0 else 1)
