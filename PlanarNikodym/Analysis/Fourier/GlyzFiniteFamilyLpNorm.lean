import PlanarNikodym.Analysis.Fourier.GlyzLpL1Error
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Exact real norm identities for a finite family and a common scalar. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_finite_family_lpNorm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (N : ℕ) (H : Fin N × X → ℂ)
    (hH : Measurable H) {p : ℝ≥0} (hp : 0 < p)
    (hf : ∀ i : Fin N, MemLp (fun x => H (i, x)) p μ) :
    lpNorm H p (Measure.count.prod μ) =
      (∑ i : Fin N, lpNorm (fun x => H (i, x)) p μ ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
  have hpR : (0 : ℝ) < p := hp
  have hfin (i : Fin N) : (∫⁻ x, ‖H (i, x)‖ₑ ^ (p : ℝ) ∂μ) ≠ ⊤ := by
    rw [← eLpNorm_nnreal_pow_eq_lintegral hp.ne']
    exact ENNReal.rpow_ne_top_of_nonneg p.coe_nonneg (hf i).eLpNorm_ne_top
  rw [← toReal_eLpNorm hH.aestronglyMeasurable,
    eLpNorm_nnreal_eq_lintegral hp.ne', ← ENNReal.toReal_rpow,
    lintegral_prod _ (hH.enorm.pow_const (p : ℝ)).aemeasurable,
    lintegral_count, tsum_fintype, ENNReal.toReal_sum (fun i _ => hfin i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← eLpNorm_nnreal_pow_eq_lintegral hp.ne', ← ENNReal.toReal_rpow,
    toReal_eLpNorm (hf i).aestronglyMeasurable]

theorem glyz_finite_rpow_scalar (N : ℕ) (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) :
    (∑ i : Fin N, (c * a i) ^ p) ^ (1 / p) =
      c * (∑ i : Fin N, (a i) ^ p) ^ (1 / p) := by
  simp_rw [Real.mul_rpow hc (ha _)]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hc p)
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (ha i) p)),
    ← Real.rpow_mul hc, mul_one_div_cancel hp.ne', Real.rpow_one]

end PlanarNikodym
