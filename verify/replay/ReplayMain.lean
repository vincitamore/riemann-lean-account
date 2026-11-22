/-
A full kernel replay of everything a module imports, into an environment that starts empty.

What it does. It imports the root module (`Main` unless another is named) once, as a file
outside Lean's module system imports it, and takes every constant of every module in the import
closure (for `Main`: the archive, Mathlib and its dependencies, and Lean's own library). The
constants that Lean marks unsafe or partial are set aside and listed; no replay examines them.
The others are put in a dependency order, and each declaration is passed to the Lean kernel
(`Kernel.Environment.addDeclCore`) against an environment that contains only declarations
earlier in that order. Constructors and recursors are not sent: the kernel generates them from
the inductive declarations.

When every declaration has been sent, the environment the kernel built is compared with the
parts replayed, constant by constant and in both directions: every constant of those parts
that is neither unsafe nor partial, in the version that Lean's import keeps of its name, must
equal, field by field, the constant of that name in the environment the kernel built, and
every constant the kernel built must be one of them. Terms are compared up to the
names and annotations of binders, which the kernel does not consult. Without this comparison a
file could hold a constant that no kernel call produces (an inductive type or a quotient
constant written into the table directly), and it would be counted and never examined.

A module that uses Lean's module system is compiled to five files. An import from outside the
module system reads the private part (`.olean.private`), and that is the part replayed; a
module inside the system that imports with `import all` reads it too. Otherwise a
module inside the system receives its constants from elsewhere: from the first part (`.olean`),
from the modules that the first part's import list names, and, for a module loaded only for
its compiled code, from the `.ir` file and from the modules that its import list names
(`Lean/Environment.lean`: `readModuleDataPartsOfMod`,
`ImportedModule.mainModule?`, `importModulesCore`). The constants of the server part reach no
kernel environment, and it is not read here. Lean writes the first part from the same
declarations, each unchanged, reduced to an axiom with the same statement, or left out; it
gives the first part and the `.ir` file the import list of the private part; and `lean`
writes no constants into the `.ir` and `.ir.sig` files. The program fails unless all of that
holds: every constant of the first part is the constant of that name in the private part or
its statement as such an axiom; the private part carries the module-system flag when the
first part does; the import lists of the first part and of the `.ir` file are that of the
private part; and the code files hold no constants.
The axiom must be marked unsafe exactly when the source of Lean 4.33.1 marks it so, with one
allowance: the files of Lean's own library, as distributed with 4.33.1, do not mark the axiom
of a partial definition, though files that 4.33.1 compiles do. In the files of the toolchain's
library the program accepts the unmarked form and counts it. A partial definition is not
replayed (below), so such an axiom states a type that this program has not passed to the
kernel; and a theorem of a module inside the module system may use it.

What is not compared in those files: the entries of environment extensions and the names
listed for the compiler. At import they add no constant to a kernel environment. They do
reach the elaborator and the compiler of a module inside the system, which may run compiled
code found there, and the names listed for the compiler decide which recorded list of axioms
`#print axioms` reads.

Memory. The first part and the code files are read a second time while the import keeps them
mapped, so each is copied; the copies are kept to the end. On the closure of Lean's own
library that is about 650 MB.

How it differs from the toolchain's `leanchecker`.
* `leanchecker` re-imports the import closure once for every module it checks, all at once. On
  an archive of 175,187 modules, nearly every one importing nearly all of the others, that
  exceeds memory.
* `leanchecker --fresh` replays one module's closure in one process, as this program does, on
  one thread, and stops at the first failure.
* Here the checks run in parallel. For a definition, theorem, opaque constant or axiom, the
  kernel check runs in a task against a snapshot of the environment, while the main thread adds
  the same declaration with `addDeclWithoutChecking` and moves on. Each declaration is therefore
  checked by the kernel against exactly the declarations before it, which is what a sequential
  replay does; only the schedule differs. Inductive types and the quotient type are added,
  checked, on the main thread.
* `Lean.Environment.replay`, which `leanchecker` calls, compares constructors and recursors with
  the kernel's and nothing else. The comparison described above also covers inductive types and
  quotient constants; the program also requires every listed constructor to be a constructor of
  its type, every stored name to be the name of its constant, and the files from which a
  module inside the module system takes constants to agree with the part replayed, as
  described above.

A name declared by more than one module: Lean's import accepts this for two theorems with the
same statement, for a theorem and an axiom, and for two axioms. The program keeps the version
Lean keeps and checks every other version that has a proof against the same environment. A
further version that is an axiom has no proof to check; it must have the statement of the
version kept. The program fails if two versions differ in statement, universe parameters or
safety.

Arguments: the output directory; the root module; then the names of theorems to report on. For
each of these the program requires that it was checked as a theorem, that nothing it depends on
failed, and lists the axioms it depends on, computed in the environment the kernel built.

The run ends with a self-test of the kernel call alone: it must accept `True.intro : True` and
reject `True.intro : False`. The test of the whole program is the package `../hostile`, whose
modules have compiled files that must be rejected, with controls that must be accepted.

What is trusted. The kernel. Lean's reader of compiled files, including the hashes and flags
that names and terms carry in those files, which nothing recomputes. The few constants of
Lean's library that the kernel treats specially by name.

Build (in this directory):   lake build replay
Run (from the archive root, so that LEAN_PATH points at the built archive):
    lake env /path/to/replay/.lake/build/bin/replay <output-directory> [root [theorem ...]]
Outputs: replay-summary.txt, replay-failures.txt, replay-axioms.txt, replay-skipped.txt,
replay-targets.txt. The exit code is 0 only if nothing failed.
-/
import Lean
open Lean

deriving instance BEq for InductiveVal, QuotKind, QuotVal, ConstantInfo

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

/-- Everything a constant of the environment the kernel built refers to. -/
def refsOf (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := usedConsts ci.type
  match ci with
  | .defnInfo v => out := out ++ usedConsts v.value
  | .thmInfo v => out := out ++ usedConsts v.value
  | .opaqueInfo v => out := out ++ usedConsts v.value
  | .inductInfo v => out := out ++ v.ctors.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for r in v.rules do out := out ++ usedConsts r.rhs
  | _ => pure ()
  return out

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "an axiom"
  | .defnInfo _ => "a definition"
  | .thmInfo _ => "a theorem"
  | .opaqueInfo _ => "an opaque constant"
  | .quotInfo _ => "a quotient constant"
  | .inductInfo _ => "an inductive type"
  | .ctorInfo _ => "a constructor"
  | .recInfo _ => "a recursor"

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
  axioms : Array Name := #[]
  blockSent : Std.HashSet Name := {}
  quotDone : Bool := false
  nThm : Nat := 0
  nDef : Nat := 0
  nOpq : Nat := 0
  nAx : Nat := 0
  nQuot : Nat := 0
  nBlocks : Nat := 0
  nInd : Nat := 0
  nCtor : Nat := 0
  nRec : Nat := 0
  emitted : Nat := 0
  nAlt : Nat := 0

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
  -- Every other version of a name that more than one module declares is checked as well, against
  -- the same environment. (An axiom has no proof to check; its statement is that of the version
  -- kept, which the loading step has verified.)
  for alt in alts.getD n #[] do
    let d? : Option Declaration := match alt with
      | .defnInfo i => some (.defnDecl i)
      | .thmInfo i => some (.thmDecl i)
      | .opaqueInfo i => some (.opaqueDecl i)
      | _ => none
    if let some d := d? then
      let t := spawnCheck (← get).kenv d
      modify fun s => { s with pending := s.pending.push (n, t), nAlt := s.nAlt + 1 }
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
    modify fun s => { s with nInd := s.nInd + 1 }
    -- a mutual block is sent once, when its first member is reached
    if (← get).blockSent.contains n then return
    unless info.all.contains n do
      fail n "is not a member of the mutual block it names"
      return
    let mut types : List InductiveType := []
    let mut sound := true
    for o in info.all.reverse do
      match all[o]? with
      | some (.inductInfo w) =>
        let mut ctors : List Constructor := []
        for c in w.ctors.reverse do
          match all[c]? with
          | some (.ctorInfo cv) =>
            if cv.induct != w.name || cv.isUnsafe then
              fail n s!"{c}, listed as a constructor of {o}, is a constructor of {cv.induct} or is unsafe"
              sound := false
            ctors := { name := cv.name, type := cv.type } :: ctors
          | some other =>
            fail n s!"{c}, listed as a constructor of {o}, is {kindOf other}"
            sound := false
          | none =>
            fail n s!"{c}, listed as a constructor of {o}, is not in the compiled files"
            sound := false
        types := { name := w.name, type := w.type, ctors := ctors } :: types
      | _ =>
        fail n s!"member {o} of the mutual block is missing or is not an inductive type"
        sound := false
    modify fun s => { s with blockSent := info.all.foldl (fun acc o => acc.insert o) s.blockSent }
    if sound then
      modify fun s => { s with nBlocks := s.nBlocks + 1 }
      checkedNow n (.inductDecl info.levelParams info.numParams types false)
  -- not sent: the kernel generates them, and the final comparison examines each
  | .ctorInfo _ => modify fun s => { s with nCtor := s.nCtor + 1 }
  | .recInfo _ => modify fun s => { s with nRec := s.nRec + 1 }
  | .quotInfo _ =>
    -- the quotient type is one kernel declaration that provides four constants
    modify fun s => { s with nQuot := s.nQuot + 1 }
    unless (← get).quotDone do
      modify fun s => { s with quotDone := true }
      checkedNow n .quotDecl

/-- May two modules both declare a name with these two constants? Lean's import allows two
theorems, a theorem and an axiom, and two axioms (and refuses two definitions or two opaque
constants before this program runs); here they must also agree in statement, universe
parameters and safety. -/
def versionsAgree (a b : ConstantInfo) : Bool :=
  let kinds := match a, b with
    | .thmInfo _, .thmInfo _ | .thmInfo _, .axiomInfo _ | .axiomInfo _, .thmInfo _ | .axiomInfo _, .axiomInfo _ => true
    | .defnInfo _, .defnInfo _ | .opaqueInfo _, .opaqueInfo _ => true
    | _, _ => false
  kinds && a.type == b.type && a.levelParams == b.levelParams && a.isUnsafe == b.isUnsafe
    && a.isPartial == b.isPartial

/-- Is `e`, a constant of the first part of a module-system file, what Lean writes there for
the constant `p` of the private part? Lean writes `p` itself or, for a theorem, a definition or
an opaque constant, an axiom with the same name, universe parameters and statement
(`Lean/AddDecl.lean`, `addDeclCore`). The axiom of a theorem is not
marked unsafe, and that of an unsafe definition or opaque constant is. For a partial
definition (the form of a recursive definition that Lean compiles to code), the source of
Lean 4.33.1 marks the axiom unsafe, and files that 4.33.1 compiles do; the files of Lean's own
library, as distributed, leave it unmarked. `core` says that the module is one of those files,
and only there is the unmarked form allowed. -/
def exportedForm (core : Bool) (p e : ConstantInfo) : Bool :=
  e == p || match e with
    | .axiomInfo a =>
      a.name == p.name && a.levelParams == p.levelParams && a.type == p.type && (match p with
        | .thmInfo _ => !a.isUnsafe
        | .defnInfo d => (match d.safety with
          | .safe => !a.isUnsafe
          | .unsafe => a.isUnsafe
          | .partial => a.isUnsafe || core)
        | .opaqueInfo o => a.isUnsafe == o.isUnsafe
        | _ => false)
    | _ => false

/-- Do two import lists agree, entry by entry? -/
def sameImports (a b : Array Import) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) =>
    x.module == y.module && x.importAll == y.importAll && x.isExported == y.isExported
      && x.isMeta == y.isMeta

unsafe def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "."
  -- the module whose import closure is replayed; `Main` unless a second argument names another
  let root := (args.getD 1 "Main").toName
  let targets := (args.drop 2).map String.toName
  let window := ((← IO.getEnv "REPLAY_WINDOW").bind String.toNat?).getD 20000
  let sysroot ← findSysroot
  initSearchPath sysroot
  -- the toolchain's library, by its real path and with a separator, for the allowance above
  let coreLib := (← IO.FS.realPath (sysroot / "lib" / "lean")).toString ++ System.FilePath.pathSeparator.toString
  let t0 ← IO.monoMsNow
  say s!"importing {root}"
  let env ← importModules #[{ module := root }] {} (trustLevel := 1024)
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut all : Std.HashMap Name ConstantInfo := {}
  let mut names : Array Name := #[]
  let mut alts : Std.HashMap Name (Array ConstantInfo) := {}
  let mut early : Array (Name × String) := #[]
  let mut dup := 0
  let mut nPartModules := 0
  let mut nExported := 0
  let mut nPartialUnmarked := 0
  let mut nIrModules := 0
  for i in [0:mods.size] do
    let md := data[i]!
    if md.constNames.size != md.constants.size then
      early := early.push (mods[i]!, "the module's list of names and its list of constants differ in length")
    for j in [0:min md.constNames.size md.constants.size] do
      let n := md.constNames[j]!
      let ci := md.constants[j]!
      if ci.name != n then
        early := early.push (n, s!"the compiled file stores under this name a constant named {ci.name}")
      match all[n]? with
      | some prev =>
        dup := dup + 1
        unless versionsAgree prev ci do
          early := early.push (n, s!"two modules declare this name, as {kindOf prev} and as {kindOf ci}, and the two differ in kind, statement, universe parameters or safety")
        -- keep what Lean's import keeps: a theorem over an axiom, otherwise the later one
        let keepPrev := match prev, ci with
          | .thmInfo _, .axiomInfo _ => true
          | _, _ => false
        if keepPrev then
          alts := alts.insert n ((alts.getD n #[]).push ci)
        else
          alts := alts.insert n ((alts.getD n #[]).push prev)
          all := all.insert n ci
      | none =>
        names := names.push n
        all := all.insert n ci
    -- What a module inside the module system can receive from this module's files, which the
    -- replay above does not see (the header gives the rule and where Lean's import follows it).
    let mod := mods[i]!
    let mFile ← findOLean mod
    -- Lean's import reads the private part exactly when the first part's flag is set, and has
    -- already failed if the flag is set and there is no private part. So a file without a
    -- private part has no flag, every importer receives its one part, and `md` is that part.
    if (← (OLeanLevel.private.adjustFileName mFile).pathExists) then
      match ← (readModuleData mFile).toBaseIO with
      | .error ex => early := early.push (mod, s!"the first part of the compiled file cannot be read again: {ex}")
      | .ok (first, _) =>
        if first.isModule then
          nPartModules := nPartModules + 1
          unless md.isModule do
            early := early.push (mod, "the first part of the compiled file is marked as a module-system file and the private part is not")
          unless sameImports first.imports md.imports do
            early := early.push (mod, "the import list of the first part of the compiled file differs from that of the private part")
          let core := (← IO.FS.realPath mFile).toString.startsWith coreLib
          let mut own : Std.HashMap Name ConstantInfo := {}
          for j in [0:min md.constNames.size md.constants.size] do
            own := own.insert md.constNames[j]! md.constants[j]!
          if first.constNames.size != first.constants.size then
            early := early.push (mod, "the first part's list of names and its list of constants differ in length")
          for j in [0:min first.constNames.size first.constants.size] do
            let n := first.constNames[j]!
            let e := first.constants[j]!
            nExported := nExported + 1
            -- (given the same test on the private part, above, and the test of names in
            -- `exportedForm`, this one can fail only when one of those also does)
            if e.name != n then
              early := early.push (n, s!"the first part of module {mod} stores under this name a constant named {e.name}")
            match own[n]? with
            | some p =>
              if exportedForm core p e then
                if p.isPartial && !e.isUnsafe && !(e == p) then nPartialUnmarked := nPartialUnmarked + 1
              else
                early := early.push (n, s!"the first part of module {mod} holds {kindOf e} of this name that is neither the constant replayed nor its statement as an axiom")
            | none =>
              early := early.push (n, s!"the first part of module {mod} holds {kindOf e} of this name, and the part replayed holds none")
    -- The files of compiled code. Lean's import reads them whenever the first exists.
    let irSig := mFile.withExtension "ir.sig"
    let ir := mFile.withExtension "ir"
    if (← irSig.pathExists) then
      nIrModules := nIrModules + 1
      let files := if (← ir.pathExists) then #[irSig, ir] else #[irSig]
      match ← (readModuleDataParts files).toBaseIO with
      | .error ex => early := early.push (mod, s!"the files of compiled code cannot be read: {ex}")
      | .ok parts =>
        for (pd, _) in parts do
          if pd.constants.size != 0 || pd.constNames.size != 0 then
            early := early.push (mod, s!"a file of compiled code of this module holds {pd.constants.size} constants; Lean writes none there")
        -- the `.ir` file can stand as the module's main data, and then its import list is followed
        if let some (pd, _) := parts[1]? then
          unless sameImports pd.imports md.imports do
            early := early.push (mod, "the import list of the `.ir` file differs from that of the part replayed")
  -- safety is decided on the version kept
  let mut order : Array Name := #[]
  let mut skipped : Array Name := #[]
  for n in names do
    let ci := all[n]!
    if ci.isUnsafe || ci.isPartial then skipped := skipped.push n else order := order.push n
  let mut altAxioms : Array Name := #[]
  for (n, vs) in alts.toList do
    for v in vs do
      if let .axiomInfo _ := v then altAxioms := altAxioms.push n
  let depsFor (n : Name) (ci : ConstantInfo) : Array Name :=
    (alts.getD n #[]).foldl (fun acc a => acc ++ depsOf all a) (depsOf all ci)
  say s!"modules {mods.size}, constants {all.size}, to replay {order.size}, unsafe or partial (not replayed) {skipped.size}, further versions of names already declared {dup}, {((← IO.monoMsNow) - t0) / 1000} s"
  let fresh ← mkEmptyEnvironment
  let init : St := { kenv := fresh.toKernelEnv }
  let (_, st) ← (do
    for (n, msg) in early do fail n msg
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
    say s!"all declarations checked, {((← IO.monoMsNow) - t0) / 1000} s; comparing the environment the kernel built with the compiled files"
    -- every constant of the files that is neither unsafe nor partial must be the constant of
    -- that name in the environment the kernel built
    let kenv := (← get).kenv
    for n in order do
      match kenv.find? n with
      | none => fail n s!"is {kindOf all[n]!} in the compiled files, and the kernel produced no constant of this name"
      | some k =>
        unless k == all[n]! do
          fail n s!"is {kindOf all[n]!} in the compiled files and differs from the constant the kernel produced ({kindOf k})"
    -- and the kernel must have produced nothing else
    let inOrder : Std.HashSet Name := order.foldl (fun acc n => acc.insert n) {}
    let extra := kenv.constants.fold (fun acc n _ => if inOrder.contains n then acc else acc.push n) (#[] : Array Name)
    for n in extra do
      fail n "was produced by the kernel and is not a constant of the compiled files that is neither unsafe nor partial"
    : M Unit).run init
  -- the theorems asked about: each must have been checked as a theorem, and nothing it depends
  -- on may have failed
  let failed : Std.HashSet Name := st.failures.foldl (fun acc (n, _) => acc.insert n) {}
  let mut targetsOut := ""
  let mut targetsOk := true
  for t in targets do
    match st.kenv.find? t, all[t]? with
    | some (.thmInfo _), some (.thmInfo _) =>
      -- what it depends on, and its axioms, in the environment the kernel built
      let mut seen : Std.HashSet Name := {}
      let mut todo : Array Name := #[t]
      let mut ax : Array Name := #[]
      let mut bad : Array Name := #[]
      while !todo.isEmpty do
        let x := todo.back!
        todo := todo.pop
        if seen.contains x then continue
        seen := seen.insert x
        if failed.contains x then bad := bad.push x
        match st.kenv.find? x with
        | some ci =>
          if let .axiomInfo _ := ci then ax := ax.push x
          for d in refsOf ci do
            unless seen.contains d do todo := todo.push d
        -- absent: a name that the traversal adds for literals and this library does not declare
        | none => pure ()
      if bad.isEmpty then
        let axs := (ax.map toString).qsort (· < ·)
        targetsOut := targetsOut ++ s!"{t}: a theorem, checked by the kernel; it depends on {seen.size} constants; axioms: {axs.toList}\n"
      else
        targetsOk := false
        targetsOut := targetsOut ++ s!"{t}: FAILED: {bad.size} of the constants it depends on failed, the first being {bad[0]!}\n"
    | _, _ =>
      targetsOk := false
      targetsOut := targetsOut ++ s!"{t}: NOT a theorem of the compiled files and of the environment the kernel built\n"
  -- self-test of the check itself, against the final environment
  let good : Declaration := .thmDecl { name := `_replay_selftest_true, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  let bad : Declaration := .thmDecl { name := `_replay_selftest_false, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  let rGood ← IO.wait (spawnCheck st.kenv good)
  let rBad ← IO.wait (spawnCheck st.kenv bad)
  let okGood := rGood.isNone
  let okBad := rBad.isSome
  let secs := ((← IO.monoMsNow) - t0) / 1000
  let threads := (← IO.getEnv "LEAN_NUM_THREADS").getD "unset (Lean's default: one per processor)"
  let counted := st.nThm + st.nDef + st.nOpq + st.nAx + st.nQuot + st.nInd + st.nCtor + st.nRec
  let balanced := counted == order.size && st.emitted == order.size
  let mut out := s!"REPLAY-SUMMARY\nroot {root}\nthreads {threads}\nmodules {mods.size}\nconstants {all.size}\nreplayed {order.size}\n"
  out := out ++ s!"theorems {st.nThm}\ndefinitions {st.nDef}\nopaque {st.nOpq}\naxioms {st.nAx}\nquotient-constants {st.nQuot}\n"
  out := out ++ s!"inductive-types {st.nInd} in {st.nBlocks} blocks\nconstructors-compared {st.nCtor}\nrecursors-compared {st.nRec}\n"
  out := out ++ s!"sum-of-the-kinds {counted} (equals replayed: {balanced})\n"
  out := out ++ s!"compared-with-the-kernel's-constants {order.size} (every constant replayed, in both directions)\n"
  out := out ++ s!"exported-parts-compared {nPartModules} modules, {nExported} constants\n"
  out := out ++ s!"exported-axioms-of-partial-definitions-not-marked-unsafe {nPartialUnmarked} (allowed in Lean's own library only)\n"
  out := out ++ s!"code-files-read {nIrModules} modules (they must hold no constants)\n"
  out := out ++ s!"unsafe-or-partial-not-replayed {skipped.size}\nfailed {st.failures.size}\n"
  out := out ++ s!"names-declared-more-than-once {alts.size}, further versions {dup}, of which checked {st.nAlt} and axioms {altAxioms.size}\n"
  out := out ++ s!"selftest accepts-true {okGood} rejects-false {okBad}\nseconds {secs}\n"
  IO.FS.writeFile (outDir ++ "/replay-summary.txt") out
  IO.FS.writeFile (outDir ++ "/replay-failures.txt")
    (String.intercalate "\n" (st.failures.toList.map fun (n, m) => s!"{n}\t{m.replace "\n" " "}"))
  IO.FS.writeFile (outDir ++ "/replay-axioms.txt")
    (String.intercalate "\n" ((st.axioms ++ altAxioms).toList.map toString))
  IO.FS.writeFile (outDir ++ "/replay-skipped.txt") (String.intercalate "\n" (skipped.toList.map toString))
  IO.FS.writeFile (outDir ++ "/replay-targets.txt") targetsOut
  say out
  say targetsOut
  let ok := st.failures.isEmpty && okGood && okBad && balanced && targetsOk
  say s!"REPLAY-DONE failed={st.failures.size} selftest={okGood && okBad} balanced={balanced} targets={targetsOk} ok={ok}"
  return (if ok then 0 else 1)
