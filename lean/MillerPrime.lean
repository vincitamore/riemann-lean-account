import Targets

namespace CarryForward.Targets

/-- Repeated squaring in a field reaches one either at the initial
element or immediately after minus one. -/
private theorem first_square_root {K : Type*} [Field K] (z : K) (s : ℕ)
    (h : z ^ (2 ^ s) = 1) :
    z = 1 ∨ ∃ r < s, z ^ (2 ^ r) = -1 := by
  induction s with
  | zero => exact Or.inl (by simpa using h)
  | succ s ih =>
    rw [pow_succ, pow_mul] at h
    rcases sq_eq_one_iff.mp h with hone | hminus
    · rcases ih hone with hz | ⟨r, hr, hv⟩
      · exact Or.inl hz
      · exact Or.inr ⟨r, Nat.lt_trans hr (Nat.lt_succ_self s), hv⟩
    · exact Or.inr ⟨s, Nat.lt_succ_self s, hminus⟩

/-- The forward direction underlying MillerTestIsCorrect holds for every
nonzero base below the prime, without a bound on its logarithm. -/
theorem isStrongProbablePrime_of_prime {p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hap : a < p) : IsStrongProbablePrime p a := by
  let : Fact p.Prime := ⟨hp⟩
  let s := (p - 1).factorization 2
  let d := (p - 1) / 2 ^ s
  have hne : (a : ZMod p) ≠ 0 := fun hz =>
    (Nat.not_dvd_of_pos_of_lt ha hap) ((ZMod.natCast_eq_zero_iff a p).mp hz)
  have hd : d * 2 ^ s = p - 1 :=
    Nat.div_mul_cancel (Nat.ordProj_dvd (p - 1) 2)
  have hpow : ((a : ZMod p) ^ d) ^ (2 ^ s) = 1 := by
    rw [← pow_mul, hd]
    exact ZMod.pow_card_sub_one_eq_one hne
  rcases first_square_root ((a : ZMod p) ^ d) s hpow with hz | ⟨r, hr, hv⟩
  · exact Or.inl hz
  · refine Or.inr ⟨r, hr, ?_⟩
    change (a : ZMod p) ^ (2 ^ r * d) = -1
    rwa [Nat.mul_comm, pow_mul]

#print axioms isStrongProbablePrime_of_prime

end CarryForward.Targets
