import PlanarNikodym.Geometry.LocalCoordinates
import PlanarNikodym.Analysis.Jets.CutoffGraphJetBounds

/-! A local inverse with the frozen variables retained as coordinates.
The inverse is jointly analytic, rather than a separately chosen inverse
for every value of the frozen variables. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace PlanarNikodym

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace P] [CompleteSpace E]

def retainedParameterMap (F : P × E → E) (x : P × E) : P × E := (x.1, F x)

omit [CompleteSpace P] [CompleteSpace E] in
theorem retainedParameterMap_fderiv_isInvertible {F : P × E → E} {x : P × E}
    (hF : DifferentiableAt ℝ F x)
    (hi : (fderiv ℝ (fun z => F (x.1, z)) x.2).IsInvertible) :
    (fderiv ℝ (retainedParameterMap F) x).IsInvertible := by
  obtain ⟨B, hB⟩ := hi
  let A := fderiv ℝ F x
  let L : (P × E) →L[ℝ] (P × E) := (ContinuousLinearMap.fst ℝ P E).prod A
  let M : (P × E) →L[ℝ] (P × E) := (ContinuousLinearMap.fst ℝ P E).prod
    (B.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.snd ℝ P E) -
        (A.comp (ContinuousLinearMap.inl ℝ P E)).comp (ContinuousLinearMap.fst ℝ P E)))
  have hs (z : E) : A (0, z) = B z := by
    have harg : HasFDerivAt (fun z : E => (x.1, z))
        (ContinuousLinearMap.inr ℝ P E) x.2 := by
      convert (hasFDerivAt_const (𝕜 := ℝ) x.1 x.2).prodMk
        (hasFDerivAt_id (𝕜 := ℝ) x.2) using 1 <;> rfl
    have hd := (hF.hasFDerivAt.comp x.2 harg).fderiv
    dsimp only [Function.comp_def] at hd
    rw [← hB] at hd
    exact congrArg (fun T : E →L[ℝ] E => T z) hd.symm
  have hsum (p : P) (z : E) : A (p, z) = A (p, 0) + B z := by
    rw [← hs, ← map_add]; simp
  have hML : Function.LeftInverse M L := by
    rintro ⟨p, z⟩
    change (p, B.symm (A (p, z) - A (p, 0))) = (p, z)
    rw [hsum, add_sub_cancel_left, B.symm_apply_apply]
  have hLM : Function.RightInverse M L := by
    rintro ⟨p, z⟩
    change (p, A (p, B.symm (z - A (p, 0)))) = (p, z)
    rw [hsum, B.apply_symm_apply, add_sub_cancel]
  have hder : fderiv ℝ (retainedParameterMap F) x = L :=
    (hasFDerivAt_fst.prodMk hF.hasFDerivAt).fderiv
  rw [hder]
  exact ⟨ContinuousLinearEquiv.equivOfInverse L M hML hLM, rfl⟩

theorem exists_retainedParameter_analytic_chart {F : P × E → E} {x : P × E}
    (hF : AnalyticAt ℝ F x)
    (hi : (fderiv ℝ (fun z => F (x.1, z)) x.2).IsInvertible)
    (U : Set (P × E)) (hU : U ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph (P × E) (P × E),
      x ∈ e.source ∧ e.source ⊆ U ∧
      (∀ z, e z = (z.1, F z)) ∧
      AnalyticOnNhd ℝ e e.source ∧ AnalyticOnNhd ℝ e.symm e.target ∧
      ∀ y ∈ e.target, (e.symm y).1 = y.1 ∧ F (e.symm y) = y.2 := by
  obtain ⟨e, hx, hsub, he, ha, hb⟩ := exists_analytic_chart (retainedParameterMap F) x
    (analyticAt_fst.prod hF) (retainedParameterMap_fderiv_isInvertible hF.differentiableAt hi) U hU
  refine ⟨e, hx, hsub, he, ha, hb, ?_⟩
  intro y hy
  have hr := e.right_inv hy
  rw [he] at hr
  change ((e.symm y).1, F (e.symm y)) = y at hr
  constructor
  · simpa only [] using congrArg (fun z : P × E => z.1) hr
  · simpa only [] using congrArg (fun z : P × E => z.2) hr

/-- Restrict a retained-parameter chart to one fiber. Its inverse is the
restriction of the jointly defined inverse, with no new choice. -/
def retainedParameterFiber (e : OpenPartialHomeomorph (P × E) (P × E))
    (he : ∀ x, (e x).1 = x.1) (p : P) : OpenPartialHomeomorph E E where
  toFun z := (e (p, z)).2
  invFun y := (e.symm (p, y)).2
  source := {z | (p, z) ∈ e.source}
  target := {y | (p, y) ∈ e.target}
  map_source' := by
    intro z hz
    change (p, (e (p, z)).2) ∈ e.target
    have heq : (p, (e (p, z)).2) = e (p, z) := Prod.ext (he (p, z)).symm rfl
    rw [heq]
    exact e.map_source hz
  map_target' := by
    intro y hy
    have hr := congrArg (fun x : P × E => x.1) (e.right_inv hy)
    rw [he] at hr
    change (p, (e.symm (p, y)).2) ∈ e.source
    have heq : (p, (e.symm (p, y)).2) = e.symm (p, y) := Prod.ext hr.symm rfl
    rw [heq]
    exact e.map_target hy
  left_inv' := by
    intro z hz
    have heq : (p, (e (p, z)).2) = e (p, z) := Prod.ext (he (p, z)).symm rfl
    rw [heq, e.left_inv hz]
  right_inv' := by
    intro y hy
    have hr := congrArg (fun x : P × E => x.1) (e.right_inv hy)
    rw [he] at hr
    have heq : (p, (e.symm (p, y)).2) = e.symm (p, y) := Prod.ext hr.symm rfl
    rw [heq, e.right_inv hy]
  continuousOn_toFun := by
    exact (e.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hz => hz)).snd
  continuousOn_invFun := by
    exact (e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hz => hz)).snd
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)

omit [CompleteSpace P] [CompleteSpace E] in
theorem retainedParameterFiber_analytic {e : OpenPartialHomeomorph (P × E) (P × E)}
    (he : ∀ x, (e x).1 = x.1) (ha : AnalyticOnNhd ℝ e e.source)
    (hb : AnalyticOnNhd ℝ e.symm e.target) (p : P) :
    AnalyticOnNhd ℝ (retainedParameterFiber e he p) (retainedParameterFiber e he p).source ∧
      AnalyticOnNhd ℝ (retainedParameterFiber e he p).symm (retainedParameterFiber e he p).target := by
  constructor
  · intro z hz
    exact (ContinuousLinearMap.snd ℝ P E).analyticAt _ |>.comp
      ((ha (p, z) hz).comp (f := fun z : E => (p, z))
        (analyticAt_const.prod analyticAt_id))
  · intro y hy
    exact (ContinuousLinearMap.snd ℝ P E).analyticAt _ |>.comp
      ((hb (p, y) hy).comp (f := fun y : E => (p, y))
        (analyticAt_const.prod analyticAt_id))

omit [CompleteSpace P] [CompleteSpace E] in
/-- Compact joint parameter sets control all mixed derivatives at once.
In particular the bound is uniform in the retained time center. -/
theorem exists_uniform_analytic_jet_bound {Q : Type} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] [CompleteSpace Q] {f : P × E → Q} {S K : Set (P × E)}
    (ha : AnalyticOnNhd ℝ f S) (hK : IsCompact K) (hKS : K ⊆ S) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ j f) K := by
    intro x hx
    have hd : ContDiffAt ℝ ∞ f x := (ha x (hKS hx)).contDiffAt
    exact (hd.continuousAt_iteratedFDeriv (k := j) (by exact WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top))).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨|C|, abs_nonneg _, fun x hx => (hC x hx).trans (le_abs_self C)⟩

end PlanarNikodym
