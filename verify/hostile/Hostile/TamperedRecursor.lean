/-
A module whose compiled file holds a recursor that is not the one the kernel generates.

`Hostile.Two` is declared in the ordinary way. Its recursor is then replaced, in the table of
constants, by a copy whose two computation rules are exchanged. A replay must reject this
module.
-/
import Hostile.Plant
open Lean Elab Command

inductive Hostile.Two where
  | a
  | b

run_cmd do
  let some (.recInfo r) := (← getEnv).find? ``Hostile.Two.rec | throwError "no recursor"
  Hostile.plant (.recInfo { r with rules := r.rules.reverse })
