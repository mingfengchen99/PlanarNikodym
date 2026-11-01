import PlanarNikodym.Analysis.Fourier.GlyzLpErrorConversion

/-! Passage from a frequency-power estimate to its original Lp form.
The compact-frequency error is converted to L2 only once, after the
actual dyadic iteration. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_lp_L2_of_power_bound {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (F : X → ℂ) (f : ι → X → ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) (hF : MemLp F p μ) (hf : ∀ i ∈ I, MemLp (f i) p μ)
    {g : Plane → ℂ} (hg : MemLp g 2) {J : Set Plane}
    (hJ : volume J ≠ ∞) (hgs : Function.support g ⊆ J)
    {K Λ a Q : ℝ} (hK : 0 ≤ K) (hΛ : 0 < Λ)
    (h : (∫⁻ x, ‖F x‖ₑ ^ (p : ℝ) ∂μ) ≤
      ENNReal.ofReal (K * Λ ^ ((p : ℝ) * a)) *
        (∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) ∂μ) +
      ENNReal.ofReal (K * Λ ^ (-(p : ℝ) * Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ)) :
    lpNorm F p μ ≤
      (K ^ (1 / (p : ℝ)) * max 1 (Real.sqrt (volume J).toReal)) *
        Λ ^ a * (∑ i ∈ I, lpNorm (f i) p μ ^ (p : ℝ)) ^ (1 / (p : ℝ)) +
      (K ^ (1 / (p : ℝ)) * max 1 (Real.sqrt (volume J).toReal)) *
        Λ ^ (-Q) * lpNorm g 2 volume := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hgi := integrable_of_memLp_two_support_finite hg hJ hgs
  let B : ℝ := K ^ (1 / (p : ℝ))
  let m : ℝ := ∫ y, ‖g y‖
  have hm : 0 ≤ m := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := Real.rpow_nonneg hK _
  have hroot : B ^ (p : ℝ) = K := by
    dsimp [B]
    rw [← Real.rpow_mul hK, show (1 / (p : ℝ)) * p = 1 by field_simp,
      Real.rpow_one]
  have he : ENNReal.ofReal (B * Λ ^ (-Q) * m) ^ (p : ℝ) =
      ENNReal.ofReal (K * Λ ^ (-(p : ℝ) * Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hgi]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ B * Λ ^ (-Q) * m)
      p.coe_nonneg, Real.mul_rpow (by positivity) hm,
      Real.mul_rpow hB (by positivity), hroot,
      ← Real.rpow_mul hΛ.le]
    rw [show -Q * (p : ℝ) = -(p : ℝ) * Q by ring]
    rw [ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_rpow_of_nonneg hm p.coe_nonneg]
  have h' := h
  rw [← he] at h'
  have hnorm := glyz_lp_of_power_error_bound μ I F f hp hF hf
    (show 0 ≤ K * Λ ^ ((p : ℝ) * a) by positivity)
    (show 0 ≤ B * Λ ^ (-Q) * m by positivity) h'
  have hmain : (K * Λ ^ ((p : ℝ) * a)) ^ (1 / (p : ℝ)) = B * Λ ^ a := by
    rw [Real.mul_rpow hK (by positivity), ← Real.rpow_mul hΛ.le]
    congr 2
    field_simp
  rw [hmain] at hnorm
  apply hnorm.trans
  have hmass := integral_norm_le_sqrt_measure_mul_lpNorm_two hg hJ hgs
  have hmax1 : 1 ≤ max 1 (Real.sqrt (volume J).toReal) := le_max_left _ _
  have hmaxJ : Real.sqrt (volume J).toReal ≤ max 1 (Real.sqrt (volume J).toReal) :=
    le_max_right _ _
  have hBmax : B ≤ B * max 1 (Real.sqrt (volume J).toReal) :=
    le_mul_of_one_le_right hB hmax1
  have hs : 0 ≤ ∑ i ∈ I, lpNorm (f i) p μ ^ (p : ℝ) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg lpNorm_nonneg _
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBmax (by positivity)) (Real.rpow_nonneg hs _)
  · calc
      _ ≤ B * Λ ^ (-Q) * (Real.sqrt (volume J).toReal * lpNorm g 2 volume) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ _ := by
        have hnm : 0 ≤ lpNorm g 2 volume := lpNorm_nonneg
        nlinarith [mul_le_mul_of_nonneg_left hmaxJ
          (show 0 ≤ B * Λ ^ (-Q) * lpNorm g 2 volume by positivity)]

end PlanarNikodym
