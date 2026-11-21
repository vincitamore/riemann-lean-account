/-
A module whose compiled file holds an inductive proposition that lists, as its constructor, a
name that the file binds to an unsafe definition, and a theorem proved by that name.

In the compiled file the theorem `Hostile.claimed : Hostile.Claim` is proved by an unsafe
definition, which the kernel does not allow. A replay that rebuilds `Hostile.Claim` from its
list of constructor names, without asking what those names are, has the kernel generate a safe
constructor of that name, and then the theorem is in order. All three constants are written
into the table directly. A replay must reject this module.
-/
import Hostile.Plant
open Lean Elab Command

run_cmd do
  Hostile.plant (.inductInfo
    { name := `Hostile.Claim, levelParams := [], type := mkSort Level.zero, numParams := 0,
      numIndices := 0, all := [`Hostile.Claim], ctors := [`Hostile.Claim.witness], numNested := 0,
      isRec := false, isUnsafe := false, isReflexive := false })
  Hostile.plant (.defnInfo
    { name := `Hostile.Claim.witness, levelParams := [], type := mkConst `Hostile.Claim,
      value := mkConst `Hostile.Claim.witness, hints := .opaque, safety := .unsafe,
      all := [`Hostile.Claim.witness] })
  Hostile.plant (.thmInfo
    { name := `Hostile.claimed, levelParams := [], type := mkConst `Hostile.Claim,
      value := mkConst `Hostile.Claim.witness, all := [`Hostile.claimed] })
