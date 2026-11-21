/-
The tool of the hostile modules: it writes a constant straight into the table of constants of
the module being compiled, with no call to the kernel.

Lean keeps the function that does this private (`Lean.Kernel.Environment.add`). It is reached
here by its internal name, through the evaluator. This module itself declares nothing wrong and
both checkers must accept it.
-/
import Lean
open Lean Elab Command

namespace Hostile

/-- Puts `ci` into the table of constants, unchecked, under its own name. -/
def plant (ci : ConstantInfo) : CommandElabM Unit := do
  let env ← getEnv
  let name := mkPrivateNameCore `Lean.Environment `Lean.Kernel.Environment.add
  let add ← IO.ofExcept <|
    unsafe env.evalConst (Kernel.Environment → ConstantInfo → Kernel.Environment) {} name
  setEnv (Environment.ofKernelEnv (add env.toKernelEnv ci))

/-- Adds a declaration without passing it to the kernel, by the option Lean provides for it. -/
def addUnchecked (decl : Declaration) : CommandElabM Unit := do
  match (← getEnv).addDeclCore 0 0 decl none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "the declaration was not added"

end Hostile
