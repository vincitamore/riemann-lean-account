/-
A module whose compiled file holds a constant of the kind "inductive type" whose type is the
proposition `False`.

The kernel never produces such a constant. It is written into the table directly, and it names
as its block an unsafe inductive type, which a replay does not send to the kernel. Nothing
refers to it. A module that imports this one can write `(Hostile.fakeInductive : False)`.
A replay must reject this module.
-/
import Hostile.Plant
open Lean Elab Command

unsafe inductive Hostile.Hidden : Prop

run_cmd Hostile.plant (.inductInfo
  { name := `Hostile.fakeInductive, levelParams := [], type := mkConst ``False, numParams := 0,
    numIndices := 0, all := [`Hostile.Hidden], ctors := [], numNested := 0, isRec := false,
    isUnsafe := false, isReflexive := false })
