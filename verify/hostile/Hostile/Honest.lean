/-
The control. An ordinary module with a theorem, a definition, an inductive type and a structure.
Both checkers must accept it.
-/
namespace Hostile.Honest

inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

structure Pair where
  fst : Nat
  snd : Nat

theorem size_pos (t : Tree) : 0 < t.size := by
  induction t with
  | leaf => exact Nat.one_pos
  | node l r ihl _ => exact Nat.lt_of_lt_of_le ihl (Nat.le_add_right _ _)

end Hostile.Honest
