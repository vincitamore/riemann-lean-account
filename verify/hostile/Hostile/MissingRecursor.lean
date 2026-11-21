/-
A module whose compiled file holds an inductive type and its constructors but no recursor, and a
theorem proved with the recursor. In the compiled files `Hostile.Bit.rec` does not exist, so the
kernel rejects the theorem there; a replay that rebuilds `Hostile.Bit` has the kernel generate the
recursor, and then the theorem is in order. All four constants are written into the table
directly. A replay must reject this module: the kernel's environment then holds a constant that
the compiled files do not.

(This module and `TamperedInductive` were proposed by the third review of the replay program,
which found that no other module depended on the two checks they exercise.)
-/
import Hostile.Plant
open Lean Elab Command

run_cmd do
  let bit := mkConst `Hostile.Bit
  let nat := mkConst ``Nat
  Hostile.plant (.inductInfo
    { name := `Hostile.Bit, levelParams := [], type := mkSort Level.one, numParams := 0,
      numIndices := 0, all := [`Hostile.Bit], ctors := [`Hostile.Bit.zero, `Hostile.Bit.one],
      numNested := 0, isRec := false, isUnsafe := false, isReflexive := false })
  Hostile.plant (.ctorInfo
    { name := `Hostile.Bit.zero, levelParams := [], type := bit, induct := `Hostile.Bit,
      cidx := 0, numParams := 0, numFields := 0, isUnsafe := false })
  Hostile.plant (.ctorInfo
    { name := `Hostile.Bit.one, levelParams := [], type := bit, induct := `Hostile.Bit,
      cidx := 1, numParams := 0, numFields := 0, isUnsafe := false })
  -- `Hostile.Bit.rec (motive := fun _ => Nat) 0 1 Hostile.Bit.one = 1`, by `Eq.refl 1`
  let lhs := mkApp4 (mkConst `Hostile.Bit.rec [Level.one]) (.lam `b bit nat .default)
    (mkRawNatLit 0) (mkRawNatLit 1) (mkConst `Hostile.Bit.one)
  Hostile.plant (.thmInfo
    { name := `Hostile.usesRec, levelParams := [],
      type := mkApp3 (mkConst ``Eq [Level.one]) nat lhs (mkRawNatLit 1),
      value := mkApp2 (mkConst ``Eq.refl [Level.one]) nat (mkRawNatLit 1),
      all := [`Hostile.usesRec] })
