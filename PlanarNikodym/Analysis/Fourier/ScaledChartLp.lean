import PlanarNikodym.Analysis.Fourier.ScaledChartJacobian
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Norm transport through the actual nonlinear coordinates and the
anisotropic dilation. Constants are the explicit determinant and the
positive nonlinear Jacobian bound, with no operator estimate assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem lintegral_scaled_chart_image {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : AnalyticOnNhd ℝ e e.source) {K : Set (Aux (n + 1))}
    (hK : MeasurableSet K) (hKS : K ⊆ e.source)
    (δ : ℝ) (hδ : δ ≠ 0) (F : Aux (n + 1) → ℝ≥0∞) :
    (∫⁻ w in lowerDegreeDilation n δ hδ '' (e '' K), F w) =
      ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| *
        ∫⁻ z in K, ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| *
          F (lowerDegreeDilation n δ hδ (e z)) := by
  let D := lowerDegreeDilation n δ hδ
  have heK : MeasurableSet (e '' K) := measurable_image_of_fderivWithin hK
    (fun x hx => (he x (hKS hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (e.injOn.mono hKS)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume heK
    (f' := fun _ => D.toContinuousLinearMap)
    (fun _ _ => D.hasFDerivAt.hasFDerivWithinAt) D.injective.injOn F]
  change (∫⁻ x in e '' K, ENNReal.ofReal |LinearMap.det D.toLinearMap| * F (D x)) = _
  rw [det_lowerDegreeDilation, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK
    (fun x hx => (he x (hKS hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (e.injOn.mono hKS) (fun x => F (D x))

theorem scaled_chart_lintegral_lower_bound {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : AnalyticOnNhd ℝ e e.source) {K : Set (Aux (n + 1))}
    (hK : MeasurableSet K) (hKS : K ⊆ e.source)
    {b : ℝ} (hb : 0 ≤ b)
    (hJ : ∀ z ∈ K, b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|)
    (δ : ℝ) (hδ : δ ≠ 0) (F : Aux (n + 1) → ℝ≥0∞) :
    ENNReal.ofReal (b * |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|) *
      (∫⁻ z in K, F (lowerDegreeDilation n δ hδ (e z))) ≤
        ∫⁻ w in lowerDegreeDilation n δ hδ '' (e '' K), F w := by
  rw [lintegral_scaled_chart_image e he hK hKS, ENNReal.ofReal_mul hb]
  rw [mul_comm (ENNReal.ofReal b), mul_assoc]
  apply mul_le_mul_right
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hK
  intro z hz
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ z hz)) _

theorem scaled_chart_eLpNorm_lower_bound {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : AnalyticOnNhd ℝ e e.source) {K : Set (Aux (n + 1))}
    (hK : MeasurableSet K) (hKS : K ⊆ e.source)
    {b : ℝ} (hb : 0 ≤ b)
    (hJ : ∀ z ∈ K, b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|)
    (δ : ℝ) (hδ : δ ≠ 0) (F : Aux (n + 1) → ℂ)
    (p : ℝ≥0∞) (hp : p ≠ 0) (hpt : p ≠ ∞) :
    ENNReal.ofReal (b * |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|) ^ (1 / p.toReal) *
      eLpNorm (fun z => F (lowerDegreeDilation n δ hδ (e z))) p (volume.restrict K) ≤
        eLpNorm F p (volume.restrict (lowerDegreeDilation n δ hδ '' (e '' K))) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  exact ENNReal.rpow_le_rpow
    (scaled_chart_lintegral_lower_bound e he hK hKS hb hJ δ hδ (fun w => ‖F w‖ₑ ^ p.toReal))
    (by positivity)

end PlanarNikodym
