/-
A module whose compiled file holds a constructor that is not the one the kernel generates.

`Hostile.Box` is declared in the ordinary way, with one constructor of one field. The
constructor is then replaced, in the table of constants, by a copy that claims two fields. A
replay must reject this module.
-/
import Hostile.Plant
open Lean Elab Command

inductive Hostile.Box where
  | mk : Nat → Hostile.Box

run_cmd do
  let some (.ctorInfo c) := (← getEnv).find? ``Hostile.Box.mk | throwError "no constructor"
  Hostile.plant (.ctorInfo { c with numFields := 2 })
