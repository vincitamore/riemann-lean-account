/-
A module whose compiled file holds an inductive type that lists two constructors, of which the
file contains one, and a theorem that is true only of the type with that one constructor.

`Hostile.Coin` lists `heads` and `tails`; the file has no `tails` and no recursor. The theorem
`Hostile.onlyHeads : ∀ x : Hostile.Coin, x = Hostile.Coin.heads` is proved with the recursor of
the one-constructor type. A replay that drops a listed constructor it cannot find has the
kernel build that one-constructor type and accepts the theorem. All three constants are written
into the table directly. A replay must reject this module.
-/
import Hostile.Plant
open Lean Elab Command

run_cmd do
  let coin := mkConst `Hostile.Coin
  let heads := mkConst `Hostile.Coin.heads
  let isHeads := mkApp3 (mkConst ``Eq [Level.one]) coin (.bvar 0) heads
  Hostile.plant (.inductInfo
    { name := `Hostile.Coin, levelParams := [], type := mkSort Level.one, numParams := 0,
      numIndices := 0, all := [`Hostile.Coin], ctors := [`Hostile.Coin.heads, `Hostile.Coin.tails],
      numNested := 0, isRec := false, isUnsafe := false, isReflexive := false })
  Hostile.plant (.ctorInfo
    { name := `Hostile.Coin.heads, levelParams := [], type := coin, induct := `Hostile.Coin,
      cidx := 0, numParams := 0, numFields := 0, isUnsafe := false })
  Hostile.plant (.thmInfo
    { name := `Hostile.onlyHeads, levelParams := [],
      type := .forallE `x coin isHeads .default,
      value := .lam `x coin
        (mkApp3 (mkConst `Hostile.Coin.rec [Level.zero]) (.lam `t coin isHeads .default)
          (mkApp2 (mkConst ``Eq.refl [Level.one]) coin heads) (.bvar 0)) .default,
      all := [`Hostile.onlyHeads] })
