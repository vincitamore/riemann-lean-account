import MillerSubgroup
import MillerCharacter

namespace CarryForward.Targets

/-- A small witness against every nonprincipal Dirichlet character suffices
for deterministic Miller testing up to the stated logarithmic bound. -/
theorem millerTestIsCorrect_of_smallNonresidue (h : SmallNonresidue) : MillerTestIsCorrect :=
  miller_of_liar_subgroups h isUnit_of_isStrongProbablePrime exists_proper_subgroup_of_composite

#print axioms millerTestIsCorrect_of_smallNonresidue

end CarryForward.Targets
