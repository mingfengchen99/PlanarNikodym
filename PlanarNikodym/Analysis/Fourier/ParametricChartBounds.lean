import PlanarNikodym.Geometry.ParametricAnalyticCoordinates
import PlanarNikodym.Analysis.Fourier.ScaledChartJacobian

/-! Uniform bounds on the actual fiber Jacobians and the complete jets
of a joint analytic chart and its inverse. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace PlanarNikodym

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

def fiberChartJacobian {m : ℕ}
    (e : OpenPartialHomeomorph (P × Aux m) (P × Aux m)) (x : P × Aux m) : ℝ :=
  LinearMap.det (fderiv ℝ (fun z => (e (x.1, z)).2) x.2).toLinearMap

theorem continuousOn_fiberChartJacobian {m : ℕ}
    (e : OpenPartialHomeomorph (P × Aux m) (P × Aux m))
    (ha : AnalyticOnNhd ℝ e e.source) : ContinuousOn (fiberChartJacobian e) e.source := by
  intro x hx
  have hswap : ContDiffAt ℝ ∞ (fun y : Aux m × P => (e (y.2, y.1)).2) (x.2, x.1) :=
    ((ha x hx).contDiffAt (n := ∞) |>.comp (x.2, x.1)
      (contDiffAt_snd.prodMk contDiffAt_fst)).snd
  have hD : ContinuousAt (fun y : P × Aux m =>
      fderiv ℝ (fun z => (e (y.1, z)).2) y.2) x :=
    (contDiffAt_fiber_fderiv hswap).continuousAt.comp
      (f := fun y : P × Aux m => (y.2, y.1))
      (continuous_snd.prodMk continuous_fst).continuousAt
  exact (ContinuousLinearMap.continuous_det.continuousAt.comp hD).continuousWithinAt

theorem exists_uniform_fiberChartJacobian_bounds {m : ℕ}
    (e : OpenPartialHomeomorph (P × Aux m) (P × Aux m))
    (he : ∀ x, (e x).1 = x.1) (ha : AnalyticOnNhd ℝ e e.source)
    (hb : AnalyticOnNhd ℝ e.symm e.target)
    {K : Set (P × Aux m)} (hK : IsCompact K) (hKS : K ⊆ e.source) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ x ∈ K,
      b ≤ |fiberChartJacobian e x| ∧ |fiberChartJacobian e x| ≤ C := by
  have hc : ContinuousOn (fun x => |fiberChartJacobian e x|) K :=
    (continuousOn_fiberChartJacobian e ha).abs.mono hKS
  have hn (x : P × Aux m) (hx : x ∈ K) : 0 < |fiberChartJacobian e x| := by
    obtain ⟨ha', hb'⟩ := retainedParameterFiber_analytic he ha hb x.1
    exact abs_pos.mpr (analytic_chartJacobian_ne_zero (retainedParameterFiber e he x.1)
      ha' hb' (hKS hx))
  obtain ⟨b, hb0, hlow⟩ := hK.exists_forall_le' hc hn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨b, |C| + 1, hb0, by positivity, ?_⟩
  intro x hx
  refine ⟨hlow x hx, ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs, abs_abs] at h
  linarith [le_abs_self C]

/-- The constants depend on fixed compact joint sets, not on any value
of the retained center/frozen parameters inside those sets. -/
theorem exists_uniform_joint_chart_jet_bounds {m : ℕ}
    (e : OpenPartialHomeomorph (P × Aux m) (P × Aux m))
    (ha : AnalyticOnNhd ℝ e e.source) (hb : AnalyticOnNhd ℝ e.symm e.target)
    {K L : Set (P × Aux m)} (hK : IsCompact K) (hKS : K ⊆ e.source)
    (hL : IsCompact L) (hLT : L ⊆ e.target) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x ∈ K, ‖iteratedFDeriv ℝ j e x‖ ≤ C) ∧
      ∀ y ∈ L, ‖iteratedFDeriv ℝ j e.symm y‖ ≤ C := by
  obtain ⟨A, hA, ha'⟩ := exists_uniform_analytic_jet_bound ha hK hKS j
  obtain ⟨B, hB, hb'⟩ := exists_uniform_analytic_jet_bound hb hL hLT j
  exact ⟨max A B, hA.trans (le_max_left _ _),
    fun x hx => (ha' x hx).trans (le_max_left _ _),
    fun y hy => (hb' y hy).trans (le_max_right _ _)⟩

end PlanarNikodym
