import PlanarNikodym.Analysis.Jets.ScalarJetExpansion
import PlanarNikodym.Analysis.Fourier.BandBernstein

/-! The scalar vertical derivatives in the actual jet expansion also
satisfy Bernstein bounds derived from the already proved full band jets. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

theorem scalarJetVerticalIter_eq_iteratedFDeriv {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : Plane) :
    scalarJetVerticalIter m f x = iteratedFDeriv ℝ m f x (fun _ => (0, 1)) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have he : scalarJetVerticalIter m f = fun y =>
        iteratedFDeriv ℝ m f y (fun _ => ((0, 1) : Plane)) := funext ih
    rw [scalarJetVerticalIter_succ]
    unfold scalarJetVertical
    rw [he, fderiv_continuousMultilinear_apply_const_apply
      (hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m) x),
      iteratedFDeriv_succ_apply_left]
    rfl

theorem norm_scalarJetVerticalIter_le {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : Plane) :
    ‖scalarJetVerticalIter m f x‖ ≤ ‖iteratedFDeriv ℝ m f x‖ := by
  rw [scalarJetVerticalIter_eq_iteratedFDeriv hf]
  simpa only [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one,
    Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ m f x).le_opNorm (fun _ => ((0, 1) : Plane))

/-- This controls the actual input derivatives, independently of curve
smoothing. There is exactly one dyadic frequency factor per derivative. -/
theorem FrequencyCutoff.eLpNorm_scalarJetVerticalIter_band_le (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) {p : ℝ≥0} (hp : 1 ≤ p) (m k : ℕ) :
    eLpNorm (scalarJetVerticalIter m (L.band k f)) p volume ≤
      ENNReal.ofReal (∫ x : Plane, ‖iteratedFDeriv ℝ m (L.bandKernel 0) x‖) *
        dyadicWeight (m : ℝ) k * eLpNorm f p volume :=
  (eLpNorm_mono (norm_scalarJetVerticalIter_le (L.band_contDiff_infty k hf) m)).trans
    (L.eLpNorm_iteratedFDeriv_band_le hf hp m k)

end PlanarNikodym
