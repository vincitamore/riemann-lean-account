import MillerPrime

namespace CarryForward.Targets

private theorem character_of_proper_subgroup {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u ∈ H, χ u = 1 := by
  classical
  let e := MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ
  have hne : (e H).ofDual ≠ ⊥ := by
    intro hb
    apply hH
    apply e.injective
    rw [e.map_top]
    exact hb
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨x.val, fun h => hx (Subtype.ext h),
    MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mp x.property⟩

/-- Transfer a small character witness to the interval of bases used by Miller.
If the bound already reaches n, the least prime divisor itself is an admissible
nonunit witness. This avoids a numerical cutoff and any finite enumeration. -/
theorem miller_of_liar_subgroups (h : SmallNonresidue)
    (unit_of_pass : ∀ {n a : ℕ}, 2 < n → IsStrongProbablePrime n a → IsUnit (a : ZMod n))
    (groups : ∀ {n : ℕ}, 2 < n → Odd n → ¬n.Prime →
      ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ (a : ℕ) (u : (ZMod n)ˣ),
        (u : ZMod n) = (a : ZMod n) → IsStrongProbablePrime n a → u ∈ H) :
    MillerTestIsCorrect := by
  intro n hn ho
  constructor
  · intro hp a ha han _
    exact isStrongProbablePrime_of_prime hp (by omega) han
  intro tests
  by_contra hc
  let : NeZero n := ⟨by omega⟩
  obtain ⟨H, hH, hstrong⟩ := groups hn ho hc
  obtain ⟨χ, hχ, trivialOn⟩ := character_of_proper_subgroup H hH
  obtain ⟨a, ha, hbound, hvalue⟩ := h n χ hχ
  by_cases han : a < n
  · have ha1 : a ≠ 1 := by
      intro heq
      simp [heq] at hvalue
    have pass := tests a (by omega) han hbound.le
    obtain ⟨u, hu⟩ := unit_of_pass hn pass
    exact hvalue (hu ▸ trivialOn u (hstrong a u hu pass))
  · let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p < n := (Nat.not_prime_iff_minFac_lt (by omega)).mp hc
    have hpa : (p : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show p ≤ a by omega)
    have pass := tests p hp.two_le hpn (hpa.trans hbound.le)
    have cop := (ZMod.isUnit_iff_coprime p n).mp (unit_of_pass hn pass)
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_refl p) (Nat.minFac_dvd n)) cop

#print axioms miller_of_liar_subgroups

end CarryForward.Targets
