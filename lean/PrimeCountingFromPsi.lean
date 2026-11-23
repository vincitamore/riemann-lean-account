import Targets

open MeasureTheory Set Real

namespace CarryForward.Targets

private lemma half_le_log {t : ℝ} (ht : 2 ≤ t) : 1 / 2 ≤ log t :=
  (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ log 2).trans
    (Real.log_le_log (by norm_num) ht)

private lemma theta_error_of_psi
    (hψ : ∃ C : ℝ, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * sqrt x * log x ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ K * sqrt x * log x ^ 2 := by
  obtain ⟨C, hC⟩ := hψ
  obtain ⟨D, hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|C| + 4 * |D|, by positivity, fun x hx ↦ ?_⟩
  have hlog := half_le_log hx
  have hfactor : 1 ≤ 4 * log x ^ 2 := by nlinarith [sq_nonneg (log x - 1 / 2)]
  have hdelta : Chebyshev.psi x - Chebyshev.theta x ≤
      |D| * sqrt x * (4 * log x ^ 2) := calc
    _ ≤ D * sqrt x := hD x
    _ ≤ |D| * sqrt x := by gcongr; exact le_abs_self _
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hfactor
  calc
    |Chebyshev.theta x - x| = |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by ring_nf
    _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
    _ ≤ (|C| + 4 * |D|) * sqrt x * log x ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
      have hc : C * sqrt x * log x ^ 2 ≤ |C| * sqrt x * log x ^ 2 := by
        gcongr; exact le_abs_self _
      linarith [hC x hx, hc, hdelta]

private lemma li_parts (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, 1 / log t) - (∫ t in (2 : ℝ)..x, 1 / log t ^ 2) =
      x / log x - 2 / log 2 := by
  have hB := Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)
  have hA : IntervalIntegrable (fun t : ℝ ↦ 1 / log t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hx fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    fun_prop
  have hli : (∫ t in (2 : ℝ)..x, 1 / log t - 1 / log t ^ 2) = x / log x - 2 / log 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ t / log t) _ (hA.sub hB)
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    apply ((hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hl).congr_deriv
    simp only [id_eq]; field_simp
  rw [intervalIntegral.integral_sub hA hB] at hli
  exact hli

private noncomputable def countingKernel (t : ℝ) : ℝ := Chebyshev.theta t / (t * log t ^ 2) - 1 / log t ^ 2

private lemma integral_countingKernel_le {x K : ℝ} (hx : 2 ≤ x) (hK : 0 ≤ K)
    (hθ : ∀ t ≥ 2, |Chebyshev.theta t - t| ≤ K * sqrt t * log t ^ 2) :
    |∫ t in (2 : ℝ)..x, countingKernel t| ≤ 2 * K * sqrt x := by
  have hT := (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2
    (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hB := Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)
  have hR : IntervalIntegrable (fun t : ℝ ↦ K / sqrt t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hx fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have hs : sqrt t ≠ 0 := (Real.sqrt_pos.2 (by linarith [ht.1])).ne'
    fun_prop
  have hPrimitive : (∫ t in (2 : ℝ)..x, K / sqrt t) = 2 * K * sqrt x - 2 * K * sqrt 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ 2 * K * sqrt t) _ hR
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs := (Real.sqrt_pos.2 ht0).ne'
    convert (Real.hasDerivAt_sqrt ht0.ne').const_mul (2 * K) using 1
    field_simp
  calc
    _ ≤ ∫ t in (2 : ℝ)..x, |countingKernel t| := intervalIntegral.abs_integral_le_integral_abs hx
    _ ≤ ∫ t in (2 : ℝ)..x, K / sqrt t := by
      apply intervalIntegral.integral_mono_on hx (hT.sub hB).abs hR
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hl : 0 < log t := Real.log_pos (by linarith [ht.1])
      have hs := Real.sqrt_pos.2 ht0
      have he : countingKernel t = (Chebyshev.theta t - t) / (t * log t ^ 2) := by
        dsimp [countingKernel]; field_simp
      change |countingKernel t| ≤ K / sqrt t
      rw [he, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hl)), div_le_div_iff₀ (by positivity) hs]
      calc |Chebyshev.theta t - t| * sqrt t ≤ (K * sqrt t * log t ^ 2) * sqrt t :=
             mul_le_mul_of_nonneg_right (hθ t ht.1) hs.le
        _ = _ := by linear_combination K * log t ^ 2 * Real.sq_sqrt ht0.le
    _ ≤ _ := by rw [hPrimitive]; exact sub_le_self _ (by positivity)

private lemma assemble_error (A B D K y L : ℝ) (hK : 0 ≤ K) (hy : 1 ≤ y) (hl : 1 / 2 ≤ L)
    (ha : |A| ≤ K * y * L) (hb : |B| ≤ 2 * K * y) (hd : |D| ≤ 4) :
    |A + B + D| ≤ (5 * K + 8) * y * L := by
  calc
    _ ≤ |A + B| + |D| := abs_add_le _ _
    _ ≤ |A| + |B| + |D| := by linarith only [abs_add_le A B]
    _ ≤ K * y * L + 2 * K * y + 4 := by linarith only [ha, hb, hd]
    _ ≤ _ := by
      have hy0 : 0 ≤ y := by linarith only [hy]
      have h₁ := mul_nonneg (mul_nonneg hK hy0) (sub_nonneg.mpr hl)
      have h₂ := mul_nonneg hy0 (sub_nonneg.mpr hl)
      linarith only [h₁, h₂, hy]

/-- Abel summation converts the von Koch bound on ψ to the error bound on π. -/
theorem primeCountingError_of_psi_bound
    (hψ : ∃ C : ℝ, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * sqrt x * log x ^ 2) :
    PrimeCountingError := by
  obtain ⟨K, hK, hθ⟩ := theta_error_of_psi hψ
  refine ⟨5 * K + 8, fun x hx ↦ ?_⟩
  have hL := half_le_log hx
  have hLpos : 0 < log x := by linarith
  have hS : 1 ≤ sqrt x := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x by linarith)
  have hT := (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2
    (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hB := Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2) (by linarith : 1 < x)
  have hli := li_parts x hx
  have hI := integral_countingKernel_le hx hK hθ
  have hEnd : |(Chebyshev.theta x - x) / log x| ≤ K * sqrt x * log x := by
    rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
    simpa only [sq, mul_assoc] using hθ x hx
  have h2 : |2 / log 2| ≤ (4 : ℝ) := by
    have h := half_le_log (le_refl (2 : ℝ))
    rw [abs_of_nonneg (show 0 ≤ (2 : ℝ) / log 2 by positivity), div_le_iff₀ (show (0 : ℝ) < log 2 by positivity)]
    linarith
  have hid : (Nat.primeCounting ⌊x⌋₊ : ℝ) - (∫ t in (2 : ℝ)..x, 1 / log t) =
      (Chebyshev.theta x - x) / log x + (∫ t in (2 : ℝ)..x, countingKernel t) + 2 / log 2 := by
    simp only [countingKernel, intervalIntegral.integral_sub hT hB, Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, sub_div]
    linarith only [hli]
  exact (congrArg abs hid).le.trans
    (assemble_error _ _ _ K (sqrt x) (log x) hK hS hL hEnd hI h2)

#print axioms primeCountingError_of_psi_bound

end CarryForward.Targets
