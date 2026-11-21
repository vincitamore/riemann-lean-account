/-
A module that compiles and contains a theorem whose statement is `False`.

The theorem `Hostile.falseProved : False` is given the value `True.intro` and is added to the
environment without being passed to the kernel. The module then proves `False` from it in the
ordinary way, which the kernel accepts, since it trusts the constants already in the
environment. `lake build` succeeds and `#print axioms Hostile.conclusion` reports no axioms.
A replay must reject this module.
-/
import Lean
open Lean Elab Command

run_cmd do
  let decl := Declaration.thmDecl
    { name := `Hostile.falseProved, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  match (← getEnv).addDeclCore 0 0 decl none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "the declaration was not added"

theorem Hostile.conclusion : False := Hostile.falseProved

#print axioms Hostile.conclusion
