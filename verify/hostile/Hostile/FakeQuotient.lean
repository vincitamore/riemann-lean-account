/-
A module whose compiled file holds a constant of the kind reserved for the quotient type, under
a name of its own and with the type `False`.

The kernel never produces such a constant: it makes the four constants of the quotient type
itself, and no declaration can add another. Here one is written straight into the table of
constants. Nothing refers to it, so every declaration that is passed to a kernel is in order;
only a comparison of the compiled file's constants with the constants the kernel made can see
it. A module that imports this one can write `(Hostile.fakeQuot : False)`, and
`#print axioms` reports nothing for it. A replay must reject this module.
-/
import Hostile.Plant
open Lean Elab Command

run_cmd Hostile.plant (.quotInfo
  { name := `Hostile.fakeQuot, levelParams := [], type := mkConst ``False, kind := .type })
