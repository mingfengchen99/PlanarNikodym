import PlanarNikodym.Analysis.Maximal.E2FIONormalizedDifference
import PlanarNikodym.Analysis.Jets.CutoffGraphJetBounds

/-! Differentiating the actual normalized phase difference gives a
quantitative parameter-gradient lower bound. The diagonal value follows
from continuity and the local open patch, so nonstationarity persists
through zero separation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
namespace PlanarNikodym
variable {Q X : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def e2FIOParameterGradient (v : Fin 2 → Q) (Φ : Q × X → ℝ) (z : Q × X) : Plane :=
  (fderiv ℝ (fun q : Q => Φ (q,z.2)) z.1 (v 0),
    fderiv ℝ (fun q : Q => Φ (q,z.2)) z.1 (v 1))

theorem e2FIOParameterGradient_contDiff (v : Fin 2 → Q) {Φ : Q × X → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (e2FIOParameterGradient v Φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact ((ContinuousLinearMap.apply ℝ ℝ (v 0)).contDiff.contDiffAt.comp z
    (contDiffAt_fiber_fderiv hΦ.contDiffAt)).prodMk
    ((ContinuousLinearMap.apply ℝ ℝ (v 1)).contDiff.contDiffAt.comp z
      (contDiffAt_fiber_fderiv hΦ.contDiffAt))

variable [FiniteDimensional ℝ Q]

def e2FIONormalizedPhaseOnFiber (Φ : Q × Plane → ℝ)
    (z : Q × ((Plane × Plane) × ℝ)) : ℝ :=
  e2FIONormalizedDifference Φ (((z.1,z.2.1.1),z.2.1.2),z.2.2)

theorem e2FIONormalizedPhaseOnFiber_contDiff {Φ : Q × Plane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (e2FIONormalizedPhaseOnFiber Φ) := by
  exact (e2FIONormalizedDifference_contDiff hΦ).comp
    (((contDiff_fst.prodMk contDiff_snd.fst.fst).prodMk contDiff_snd.fst.snd).prodMk contDiff_snd.snd)

theorem e2FIOParameterGradient_difference_exact (v : Fin 2 → Q) {Φ : Q × Plane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (q : Q) (x vdir : Plane) (h : ℝ) :
    e2FIOParameterGradient v Φ (q,x+h • vdir) - e2FIOParameterGradient v Φ (q,x) =
      h • e2FIOParameterGradient v (e2FIONormalizedPhaseOnFiber Φ) (q,((x,vdir),h)) := by
  have h1 : DifferentiableAt ℝ (fun r : Q => Φ (r,x+h • vdir)) q :=
    ((hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun r : Q => Φ (r,x)) q :=
    ((hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
  have hD : DifferentiableAt ℝ
      (fun r : Q => e2FIONormalizedPhaseOnFiber Φ (r,((x,vdir),h))) q :=
    (((e2FIONormalizedPhaseOnFiber_contDiff hΦ).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp)).differentiableAt
  have he : (fun r : Q => Φ (r,x+h • vdir)-Φ (r,x)) =
      fun r : Q => h * e2FIONormalizedPhaseOnFiber Φ (r,((x,vdir),h)) := by
    funext r
    exact e2FIO_phase_difference_exact hΦ r x vdir h
  have hd := congrArg (fun f : Q → ℝ => fderiv ℝ f q) he
  have hs := fderiv_sub h1 h2
  change fderiv ℝ (fun r : Q => Φ (r,x+h • vdir)-Φ (r,x)) q = _ at hs
  rw [hs, fderiv_const_mul hD h] at hd
  apply Prod.ext
  · exact congrArg (fun L : Q →L[ℝ] ℝ => L (v 0)) hd
  · exact congrArg (fun L : Q →L[ℝ] ℝ => L (v 1)) hd

theorem e2_normalized_gradient_lower_bound_nonzero (v : Fin 2 → Q)
    {Φ : Q × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {c : ℝ}
    (q : Q) (x vdir : Plane) (h : ℝ) (hh : h ≠ 0)
    (hs : c * ‖(x+h • vdir)-x‖ ≤
      ‖e2FIOParameterGradient v Φ (q,x+h • vdir)-e2FIOParameterGradient v Φ (q,x)‖) :
    c * ‖vdir‖ ≤ ‖e2FIOParameterGradient v (e2FIONormalizedPhaseOnFiber Φ) (q,((x,vdir),h))‖ := by
  rw [e2FIOParameterGradient_difference_exact v hΦ q x vdir h, norm_smul,
    add_sub_cancel_left, norm_smul] at hs
  have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh
  exact (mul_le_mul_iff_right₀ hp).mp (by nlinarith [hs])

theorem e2_normalized_gradient_lower_bound (v : Fin 2 → Q)
    {Φ : Q × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {O : Set (Q × Plane)}
    (hO : IsOpen O) (c : ℝ)
    (hs : ∀ (q : Q) (x y : Plane), (q,x) ∈ O → (q,y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient v Φ (q,x)-e2FIOParameterGradient v Φ (q,y)‖)
    (q : Q) (x vdir : Plane) (h : ℝ) (hx : (q,x) ∈ O) (hy : (q,x+h • vdir) ∈ O) :
    c * ‖vdir‖ ≤ ‖e2FIOParameterGradient v (e2FIONormalizedPhaseOnFiber Φ) (q,((x,vdir),h))‖ := by
  by_cases hh : h = 0
  · subst h
    have hsource : Continuous (fun r : ℝ => (q,x+r • vdir)) :=
      continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const))
    have hmem : ∀ᶠ r in 𝓝 (0 : ℝ), (q,x+r • vdir) ∈ O :=
      hsource.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
    have hev : ∀ᶠ r in 𝓝[≠] (0 : ℝ), c * ‖vdir‖ ≤
        ‖e2FIOParameterGradient v (e2FIONormalizedPhaseOnFiber Φ) (q,((x,vdir),r))‖ := by
      filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hn
      exact e2_normalized_gradient_lower_bound_nonzero v hΦ q x vdir r
        (by simpa using hn) (hs q (x+r • vdir) x hr hx)
    have hcont : Continuous (fun r : ℝ =>
        ‖e2FIOParameterGradient v (e2FIONormalizedPhaseOnFiber Φ) (q,((x,vdir),r))‖) :=
      ((e2FIOParameterGradient_contDiff v (e2FIONormalizedPhaseOnFiber_contDiff hΦ)).continuous.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))).norm
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
  · exact e2_normalized_gradient_lower_bound_nonzero v hΦ q x vdir h hh
      (hs q (x+h • vdir) x hy hx)

end PlanarNikodym
