import PlanarNikodym.Analysis.Fourier.GlyzLpErrorConversion

/-! Passage from a power estimate to its original Lp form with the
actual L1 remainder. No input support restriction is needed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_lp_L1_of_power_bound {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (F : X → ℂ) (f : ι → X → ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) (hF : MemLp F p μ) (hf : ∀ i ∈ I, MemLp (f i) p μ)
    {g : Plane → ℂ} (hgi : Integrable g)
    {K Λ a Q : ℝ} (hK : 0 ≤ K) (hΛ : 0 < Λ)
    (h : (∫⁻ x, ‖F x‖ₑ ^ (p : ℝ) ∂μ) ≤
      ENNReal.ofReal (K * Λ ^ ((p : ℝ) * a)) *
        (∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) ∂μ) +
      ENNReal.ofReal (K * Λ ^ (-(p : ℝ) * Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ)) :
    lpNorm F p μ ≤
      (K ^ (1 / (p : ℝ))) *
        Λ ^ a * (∑ i ∈ I, lpNorm (f i) p μ ^ (p : ℝ)) ^ (1 / (p : ℝ)) +
      (K ^ (1 / (p : ℝ))) *
        Λ ^ (-Q) * (∫ y, ‖g y‖) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
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
  exact hnorm

end PlanarNikodym
