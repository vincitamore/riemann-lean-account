/-
A module that declares an axiom and proves `False` from it.

Nothing here evades the kernel: an axiom is a legal declaration. A replay accepts this module.
What exposes it is the list of axioms: the replay's list of axioms contains `Hostile.assumed`,
and `#print axioms Hostile.fromAxiom` names it.
-/
axiom Hostile.assumed : False

theorem Hostile.fromAxiom : False := Hostile.assumed

#print axioms Hostile.fromAxiom
