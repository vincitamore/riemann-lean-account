/-
A module that compiles and contains a definition whose value does not have its type.

`Hostile.three : Nat` is given a string as its value and is added to the environment without
being passed to the kernel; a theorem then refers to it. A replay must reject this module.
-/
import Lean
open Lean Elab Command

run_cmd do
  let decl := Declaration.defnDecl
    { name := `Hostile.three, levelParams := [], type := mkConst ``Nat, value := mkStrLit "three",
      hints := .abbrev, safety := .safe }
  match (← getEnv).addDeclCore 0 0 decl none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "the declaration was not added"

theorem Hostile.three_le : Hostile.three ≤ Hostile.three := Nat.le_refl _
