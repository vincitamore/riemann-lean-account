/-
A module whose compiled file holds an inductive type whose record is not the one the kernel
makes. `Hostile.Chain` is declared in the ordinary way and is recursive; its record is then
replaced, in the table of constants, by a copy that says it is not. A replay must reject this
module.
-/
import Hostile.Plant
open Lean Elab Command

inductive Hostile.Chain where
  | stop : Hostile.Chain
  | link : Hostile.Chain → Hostile.Chain

run_cmd do
  let some (.inductInfo v) := (← getEnv).find? ``Hostile.Chain | throwError "no inductive type"
  Hostile.plant (.inductInfo { v with isRec := false })
