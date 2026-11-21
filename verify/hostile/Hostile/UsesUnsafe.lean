/-
A module that compiles and contains a theorem whose proof uses an unsafe definition.

An unsafe definition may be anything; here it is a natural number defined by a reference to
itself. The kernel refuses a theorem that uses one, so the theorem is added without being
passed to the kernel. A replay must reject this module: it does not replay unsafe definitions,
so the theorem refers to a constant that is absent from the environment the kernel built.
-/
import Hostile.Plant
open Lean Elab Command

unsafe def Hostile.unsafeNumber : Nat := Hostile.unsafeNumber + 1

run_cmd Hostile.addUnchecked (.thmDecl
  { name := `Hostile.fromUnsafe, levelParams := [], type := mkConst ``True,
    value := mkApp (.lam `n (mkConst ``Nat) (mkConst ``True.intro) .default)
      (mkConst `Hostile.unsafeNumber) })
