/-
Which of a list of constants are in the dependency cone of `riemannHypothesis`?

`CutMain.lean` lists the cone's members only for the archive. This program computes the same
cone with the same traversal (the four definitions below are copied from `CutMain.lean`) and
says, for each name of a list, whether it is a constant of the built environment and whether it
is in the cone of `riemannHypothesis`, in the cone of the five theorems of `Main.lean` only, or
outside both. It prints the two cone sizes, which must be those of `cut-result.txt`.

Build (in this directory):   lake build coneprobe
Run (from the archive root):
    lake env /path/to/cut/.lake/build/bin/coneprobe <file with one name a line>
-/
import Lean
open Lean

def valOf : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def extraOf : ConstantInfo → List Name
  | .inductInfo v => v.ctors
  | .ctorInfo v => [v.induct]
  | _ => []

unsafe def usedConstsImpl (e : Expr) : Array Name := Id.run do
  let mut visited : Std.HashSet USize := {}
  let mut out : Std.HashSet Name := {}
  let mut stack : Array Expr := #[e]
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    match x with
    | .const n _ => out := out.insert n
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure ()
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

def cone (env : Environment) (starts : List Name) : IO (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := starts.toArray
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      for c in usedConsts ci.type do
        if !seen.contains c then stack := stack.push c
      match valOf ci with
      | some v =>
        for c in usedConsts v do
          if !seen.contains c then stack := stack.push c
      | none => pure ()
      for c in extraOf ci do
        if !seen.contains c then stack := stack.push c
  return seen

/-- A name from its printed form; a component of digits is a number, as in private names. -/
def mkName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun n c => if c ≠ "" && c.all Char.isDigit then .num n c.toNat! else .str n c) .anonymous

def main (args : List String) : IO Unit := do
  let names ← IO.FS.lines args.head!
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Main }] {} (trustLevel := 1024)
  let c ← cone env [`riemannHypothesis]
  let cAll ← cone env [`riemannHypothesis, `riemannZeta_eq_zero_re, `LFunction_ne_zero_of_half_lt_re,
    `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive]
  IO.println s!"CONE-SIZE {c.size}"
  IO.println s!"CONE-SIZE-FIVE-THEOREMS {cAll.size}"
  for s in names do
    if s.trim.isEmpty then continue
    let n := mkName s.trim
    let verdict :=
      if !env.contains n then "not a constant of this build"
      else if c.contains n then "in the cone of riemannHypothesis"
      else if cAll.contains n then "in the cone of the five theorems only"
      else "outside the cone"
    IO.println s!"{s.trim}: {verdict}"
