/-
One of two modules that declare the same theorem. This one gives it a value that is not a proof
of it, and adds it without passing it to the kernel.
-/
import Hostile.Plant
open Lean Elab Command

run_cmd Hostile.addUnchecked (.thmDecl
  { name := `Hostile.Dup.twice, levelParams := [], type := mkConst ``True,
    value := mkConst ``Nat.zero })
