import MillerPrime

namespace CarryForward.Targets

private abbrev sPart (n : ℕ) := (n - 1).factorization 2
private abbrev dPart (n : ℕ) := (n - 1) / 2 ^ sPart n

private lemma exponent_split (n : ℕ) : 2 ^ sPart n * dPart n = n - 1 := by
  rw [Nat.mul_comm]
  exact Nat.div_mul_cancel (Nat.ordProj_dvd (n - 1) 2)

private lemma carry_sign {R : Type*} [CommRing R] {z : R} {r t d : ℕ}
    (hrt : r < t) (h : z ^ (2 ^ r * d) = -1) : z ^ (2 ^ t * d) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, t = r + 1 + k := ⟨t - (r+1), by omega⟩
  subst t
  have he : 2 ^ (r + 1 + k) * d = ((2 ^ r * d) * 2) * 2 ^ k := by
    rw [pow_add, pow_succ]; ring
  rw [he, pow_mul, pow_mul, h]
  simp

theorem fermat_of_isStrongProbablePrime {n a : ℕ}
    (h : IsStrongProbablePrime n a) : (a : ZMod n) ^ (n-1) = 1 := by
  rw [← exponent_split n]
  rcases h with h | ⟨r, hr, h⟩
  · rw [Nat.mul_comm, pow_mul, h, one_pow]
  · exact carry_sign hr h

theorem isUnit_of_isStrongProbablePrime {n a : ℕ} (hn : 2 < n)
    (ha : IsStrongProbablePrime n a) : IsUnit (a : ZMod n) :=
  IsUnit.of_pow_eq_one (fermat_of_isStrongProbablePrime ha) (by omega)

private def signGroup (n e : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {u | u^e = 1 ∨ u^e = -1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change x^e = 1 ∨ x^e = -1 at hx
    change y^e = 1 ∨ y^e = -1 at hy
    change (x*y)^e = 1 ∨ (x*y)^e = -1
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [mul_pow, hx, hy]
  inv_mem' := by
    intro x hx
    change x^e = 1 ∨ x^e = -1 at hx
    change (x⁻¹)^e = 1 ∨ (x⁻¹)^e = -1
    rcases hx with hx | hx <;> simp [inv_pow, hx]

/-- CRT splices the first component of a negative witness with 1 in the
second component. Its power has mixed signs and leaves the diagonal. -/
private lemma not_full_signGroup {p q e : ℕ} (hp : 2 < p) (hq : 2 < q)
    (hc : p.Coprime q) (w : (ZMod (p*q))ˣ) (hw : w^e = -1) :
    signGroup (p*q) e ≠ ⊤ := by
  let E := ZMod.chineseRemainder hc
  let y : ZMod p × ZMod q := ((E (w : ZMod (p*q))).1, 1)
  have hunit : IsUnit y := Prod.isUnit_iff.mpr
    ⟨(w.isUnit.map E.toMonoidHom).map (MonoidHom.fst _ _), isUnit_one⟩
  let v := (hunit.map E.symm.toMonoidHom).unit
  have hv : E (v : ZMod (p*q)) = y := by
    change E (E.symm y) = y
    exact E.apply_symm_apply _
  have hwR : (w : ZMod (p*q)) ^ e = -1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.coe_neg_one] using
      congrArg (fun z : (ZMod (p*q))ˣ => (z : ZMod (p*q))) hw
  have hfirst : (E (w : ZMod (p*q))).1 ^ e = -1 := by
    simpa using congrArg (fun z => (E z).1) hwR
  intro hall
  have hvH : v ∈ signGroup (p*q) e := by rw [hall]; trivial
  change v^e = 1 ∨ v^e = -1 at hvH
  rcases hvH with h | h
  · have hR : (v : ZMod (p*q)) ^ e = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, Units.coe_neg_one] using
        congrArg (fun z : (ZMod (p*q))ˣ => (z : ZMod (p*q))) h
    have bad : (-1 : ZMod p) = 1 := by
      simpa [hv, y, hfirst] using
        congrArg (fun z => (E z).1) hR
    rcases ZMod.neg_one_eq_one_iff.mp bad with h | h <;> omega
  · have hR : (v : ZMod (p*q)) ^ e = -1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, Units.coe_neg_one] using
        congrArg (fun z : (ZMod (p*q))ˣ => (z : ZMod (p*q))) h
    have bad : (1 : ZMod q) = -1 := by
      simpa [hv, y] using congrArg (fun z => (E z).2) hR
    rcases ZMod.neg_one_eq_one_iff.mp bad.symm with h | h <;> omega

private lemma carmichael_factor {n : ℕ} (h : n.IsCarmichael) :
    ∃ p q, n = p*q ∧ 2 < p ∧ 2 < q ∧ p.Coprime q := by
  obtain ⟨q, hq⟩ := n.minFac_dvd
  have hp := Nat.minFac_prime (show n ≠ 1 by have := h.two_lt; omega)
  have hpLt := (Nat.not_prime_iff_minFac_lt (by have := h.two_lt; omega)).mp h.not_prime
  have hpodd := h.odd.of_dvd_nat n.minFac_dvd
  have hqodd := h.odd.of_dvd_nat (show q ∣ n by rw [hq]; exact dvd_mul_left _ _)
  have hq1 : q ≠ 1 := by intro h1; simp [h1] at hq; omega
  have hp2 := hp.two_le
  obtain ⟨x,hx⟩ := hpodd
  obtain ⟨y,hy⟩ := hqodd
  exact ⟨n.minFac, q, hq, by omega, by omega, Nat.coprime_of_squarefree_mul (hq ▸ h.squarefree)⟩

theorem exists_proper_subgroup_of_composite {n : ℕ} (hn : 2 < n) (_ho : Odd n)
    (hc : ¬ n.Prime) : ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧
      ∀ (a : ℕ) (u : (ZMod n)ˣ), (u : ZMod n) = (a : ZMod n) →
        IsStrongProbablePrime n a → u ∈ H := by
  classical
  let F := (powMonoidHom (α := (ZMod n)ˣ) (n-1)).ker
  by_cases hF : F = ⊤
  · have hC : n.IsCarmichael := by
      refine ⟨hn, hc, fun b hb => ?_⟩
      have hb0 : b ≠ 0 := by rintro rfl; simp at hb; omega
      apply (Nat.probablePrime_iff_zmod_one n hb0).mpr
      have H : ZMod.unitOfCoprime b hb ∈ F := by rw [hF]; trivial
      change (ZMod.unitOfCoprime b hb)^(n-1) = 1 at H
      simpa [ZMod.coe_unitOfCoprime] using
        congrArg (fun z : (ZMod n)ˣ => (z : ZMod n)) H
    obtain ⟨p,q,hpq,hp,hq,hco⟩ := carmichael_factor hC
    subst n
    let N := p*q
    let s := sPart N
    let d := dPart N
    let P := fun t : ℕ => ∃ w : (ZMod N)ˣ, w ^ (2 ^ t * d) = -1
    have hd : Odd d := Nat.not_even_iff_odd.mp
      (fun h => Nat.not_dvd_ordCompl Nat.prime_two (show N-1 ≠ 0 by dsimp [N]; omega) h.two_dvd)
    have h0 : P 0 := ⟨-1, by simp [hd.neg_one_pow]⟩
    let t := Nat.findGreatest P s
    obtain ⟨w, hw⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le s) h0
    refine ⟨signGroup N (2^t*d), not_full_signGroup hp hq hco w hw, ?_⟩
    intro a u hu ha
    change u^(2^t*d) = 1 ∨ u^(2^t*d) = -1
    rcases ha with h | ⟨r, hr, h⟩
    · left
      apply Units.ext
      change (u : ZMod N)^(2^t*d) = 1
      rw [hu, Nat.mul_comm (2^t) d, pow_mul]
      change (a : ZMod N)^d = 1 at h
      rw [h, one_pow]
    · have huR : u^(2^r*d) = -1 := by
        apply Units.ext
        change (u : ZMod N)^(2^r*d) = -1
        rwa [hu]
      have hle : r ≤ t := Nat.le_findGreatest (P := P) (le_of_lt hr) ⟨u,huR⟩
      rcases lt_or_eq_of_le hle with hlt | he
      · left
        apply Units.ext
        change (u : ZMod N)^(2^t*d) = 1
        rw [hu]; exact carry_sign hlt h
      · right; rwa [← he]
  · refine ⟨F,hF,?_⟩
    intro a u hu ha
    change u^(n-1) = 1
    apply Units.ext
    change (u : ZMod n)^(n-1) = 1
    rw [hu]; exact fermat_of_isStrongProbablePrime ha

#print axioms exists_proper_subgroup_of_composite
end CarryForward.Targets
