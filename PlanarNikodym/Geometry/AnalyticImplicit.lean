import PlanarNikodym.Geometry.LocalCoordinates

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace PlanarNikodym

theorem exists_analytic_implicit {E B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (R : E × B → B) (q : E) (w : B) (hR : AnalyticAt ℝ R (q, w))
    (hzero : R (q, w) = 0)
    (hi : ((fderiv ℝ R (q, w)).comp (ContinuousLinearMap.inr ℝ E B)).IsInvertible) :
    ∃ κ : E → B, AnalyticAt ℝ κ q ∧ κ q = w ∧
      (∀ᶠ x in 𝓝 q, R (x, κ x) = 0) ∧
      (∀ᶠ z in 𝓝 (q, w), R z = 0 ↔ κ z.1 = z.2) := by
  have hc : ContDiffAt ℝ ω R (q, w) := hR.contDiffAt
  refine ⟨hc.implicitFunction (by simp) hi,
    (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt,
    hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · simpa only [hzero] using hc.eventually_apply_implicitFunction (by simp) hi
  · simpa only [hzero] using hc.eventually_apply_eq_iff_implicitFunction (by simp) hi

theorem fderiv_snd_slice {E B F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × B → F) (p : E × B) (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun w => f (p.1, w)) p.2 =
      (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ E B) := by
  have h : HasFDerivAt (fun w : B => (p.1, w))
      (ContinuousLinearMap.inr ℝ E B) p.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1 <;> rfl
  exact (hf.hasFDerivAt.comp p.2 h).fderiv

end PlanarNikodym
