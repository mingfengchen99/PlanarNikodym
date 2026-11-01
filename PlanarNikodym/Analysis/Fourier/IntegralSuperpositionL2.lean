import PlanarNikodym.Analysis.Fourier.ComplexSymbolKernels
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! A square-integral estimate for an integrable scalar superposition.
The proof is weighted Cauchy--Schwarz followed by Tonelli, so no
boundedness of an oscillatory operator is assumed here. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem ennreal_sqrt_sq (x : ℝ≥0∞) :
    (x ^ (1 / (2 : ℝ))) ^ (2 : ℕ) = x := by
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_weighted_sq_le
    {P : Type*} [MeasurableSpace P] (μ : Measure P)
    (A G : P → ℝ≥0∞) (hA : AEMeasurable A μ) (hG : AEMeasurable G μ) :
    (∫⁻ p, A p * G p ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ p, A p ∂μ) * ∫⁻ p, A p * G p ^ (2 : ℕ) ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hA.pow_const (1 / (2 : ℝ)))
    ((hA.pow_const (1 / (2 : ℝ))).mul hG)
  have hprod (p : P) : A p ^ (1 / (2 : ℝ)) *
      (A p ^ (1 / (2 : ℝ)) * G p) = A p * G p := by
    rw [← mul_assoc, ← pow_two, ennreal_sqrt_sq]
  have hsq (p : P) :
      (A p ^ (1 / (2 : ℝ)) * G p) ^ (2 : ℝ) = A p * G p ^ (2 : ℕ) := by
    rw [ENNReal.rpow_two, mul_pow, ennreal_sqrt_sq]
  simp only [Pi.mul_apply, hprod, ENNReal.rpow_two, ennreal_sqrt_sq,
    mul_pow] at h
  have hpow := pow_le_pow_left' h 2
  simpa only [mul_pow, ennreal_sqrt_sq] using hpow

theorem lintegral_enorm_sq_integral_superposition_le
    {P W : Type*} [MeasurableSpace P] [MeasurableSpace W]
    (μ : Measure P) (ν : Measure W) [SFinite μ] [SFinite ν]
    (a : P → ℂ) (G : P → W → ℂ) (ha : Measurable a)
    (hG : Measurable (Function.uncurry G)) (B : ℝ≥0∞)
    (hB : ∀ p, (∫⁻ w, ‖G p w‖ₑ ^ (2 : ℕ) ∂ν) ≤ B) :
    (∫⁻ w, ‖∫ p, a p * G p w ∂μ‖ₑ ^ (2 : ℕ) ∂ν) ≤
      (∫⁻ p, ‖a p‖ₑ ∂μ) ^ (2 : ℕ) * B := by
  have hpoint (w : W) : ‖∫ p, a p * G p w ∂μ‖ₑ ^ (2 : ℕ) ≤
      (∫⁻ p, ‖a p‖ₑ ∂μ) * ∫⁻ p, ‖a p‖ₑ * ‖G p w‖ₑ ^ (2 : ℕ) ∂μ := by
    have hnorm : ‖∫ p, a p * G p w ∂μ‖ₑ ≤ ∫⁻ p, ‖a p‖ₑ * ‖G p w‖ₑ ∂μ := by
      simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (fun p => a p * G p w)
    exact (pow_le_pow_left' hnorm 2).trans
      (lintegral_weighted_sq_le μ _ _ ha.enorm.aemeasurable
        ((hG.comp (measurable_id.prodMk measurable_const)).enorm.aemeasurable))
  calc
    _ ≤ ∫⁻ w, (∫⁻ p, ‖a p‖ₑ ∂μ) *
        ∫⁻ p, ‖a p‖ₑ * ‖G p w‖ₑ ^ (2 : ℕ) ∂μ ∂ν := lintegral_mono hpoint
    _ = (∫⁻ p, ‖a p‖ₑ ∂μ) *
        ∫⁻ p, ‖a p‖ₑ * (∫⁻ w, ‖G p w‖ₑ ^ (2 : ℕ) ∂ν) ∂μ := by
      rw [lintegral_const_mul'']
      congr 1
      rw [lintegral_lintegral_swap]
      · apply lintegral_congr
        intro p
        exact lintegral_const_mul'' _ ((hG.comp (measurable_const.prodMk measurable_id)).enorm.pow_const _).aemeasurable
      · exact ((ha.enorm.comp measurable_snd).mul
          ((hG.comp measurable_swap).enorm.pow_const _)).aemeasurable
      · exact Measurable.lintegral_prod_left
          ((ha.enorm.comp measurable_fst).mul (hG.enorm.pow_const _)) |>.aemeasurable
    _ ≤ (∫⁻ p, ‖a p‖ₑ ∂μ) * ∫⁻ p, ‖a p‖ₑ * B ∂μ := by
      gcongr
      exact hB p
    _ = _ := by
      rw [lintegral_mul_const'', pow_two, mul_assoc]
      exact ha.enorm.aemeasurable

end PlanarNikodym
