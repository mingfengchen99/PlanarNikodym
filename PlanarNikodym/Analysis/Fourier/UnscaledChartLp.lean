import PlanarNikodym.Analysis.Fourier.ScaledChartLp

/-! Norm transport in the fixed, unscaled nonlinear jet chart. This keeps
the amplitude support fixed when the phase output carries its own linear
time-scale dilation. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem chart_lintegral_lower_bound {m : ℕ}
    (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : AnalyticOnNhd ℝ e e.source) {K : Set (Aux m)}
    (hK : MeasurableSet K) (hKS : K ⊆ e.source) {b : ℝ} (_hb : 0 ≤ b)
    (hJ : ∀ z ∈ K, b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|)
    (F : Aux m → ℝ≥0∞) :
    ENNReal.ofReal b * (∫⁻ z in K, F (e z)) ≤ ∫⁻ y in e '' K, F y := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK
    (fun z hz => (he z (hKS hz)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (e.injOn.mono hKS), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hK
  intro z hz
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ z hz)) _

theorem chart_eLpNorm_lower_bound {m : ℕ}
    (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : AnalyticOnNhd ℝ e e.source) {K : Set (Aux m)}
    (hK : MeasurableSet K) (hKS : K ⊆ e.source) {b : ℝ} (hb : 0 ≤ b)
    (hJ : ∀ z ∈ K, b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|)
    (F : Aux m → ℂ) (p : ℝ≥0∞) (hp : p ≠ 0) (hpt : p ≠ ∞) :
    ENNReal.ofReal b ^ (1 / p.toReal) *
      eLpNorm (fun z => F (e z)) p (volume.restrict K) ≤
        eLpNorm F p (volume.restrict (e '' K)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  exact ENNReal.rpow_le_rpow
    (chart_lintegral_lower_bound e he hK hKS hb hJ (fun y => ‖F y‖ₑ ^ p.toReal))
    (by positivity)

end PlanarNikodym
