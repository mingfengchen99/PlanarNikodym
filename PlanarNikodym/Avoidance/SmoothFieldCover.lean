import PlanarNikodym.Geometry.AnalyticZeros
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff
namespace PlanarNikodym

theorem graph_derivative_invertible (D : Plane →L[ℝ] ℝ) (hn : D (0, 1) ≠ 0) :
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod D).IsInvertible := by
  let L := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod D
  have hi : Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply (L.toLinearMap.ker.eq_bot_iff).mpr
    intro p hp
    change L p = 0 at hp
    have hp₁ : p.1 = 0 := congrArg Prod.fst hp
    have hp₂ : D p = 0 := congrArg Prod.snd hp
    have he : p = p.2 • ((0, 1) : Plane) := by ext <;> simp [hp₁]
    rw [he, map_smul] at hp₂
    have hs : p.2 = 0 := (mul_eq_zero.mp hp₂).resolve_right hn
    exact Prod.ext hp₁ hs
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap
    ⟨hi, LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv, rfl⟩

theorem smooth_cutoff_mul (b : Plane → ℝ) (v : Plane → Plane)
    (hb : ContDiff ℝ ∞ b) (hv : ∀ x ∈ tsupport b, ContDiffAt ℝ ∞ v x) :
    ContDiff ℝ ∞ (fun x => b x • v x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport b
  · exact hb.contDiffAt.smul (hv x hx)
  · have hzero : ∀ᶠ y in 𝓝 x, b y = 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      by_contra hn
      exact hy (subset_closure hn)
    apply (show ContDiffAt ℝ ∞ (fun _ : Plane => (0 : Plane)) x from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, zero_smul]

theorem exists_local_smooth_tangent (h : Plane → ℝ) (q : Plane)
    (ha : AnalyticAt ℝ h q) (hn : partialParameter h q ≠ 0) :
    ∃ U : Set Plane, ∃ V : Plane → Plane,
      IsOpen U ∧ q ∈ U ∧ ContDiff ℝ ∞ V ∧
      ∀ p ∈ U, V (p.1, h p) ≠ 0 ∧
        Family.wedge (V (p.1, h p)) (1, partialTime h p) = 0 := by
  let G : Plane → Plane := fun p => (p.1, h p)
  have hG : AnalyticAt ℝ G q := analyticAt_fst.prod ha
  have hd : fderiv ℝ G q = (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ h q) :=
    (hasFDerivAt_fst.prodMk ha.differentiableAt.hasFDerivAt).fderiv
  obtain ⟨e, hqe, hes, he, _, heia⟩ := exists_analytic_chart G q hG
    (hd ▸ graph_derivative_invertible (fderiv ℝ h q) hn)
    {p | AnalyticAt ℝ h p} ha.eventually_analyticAt
  obtain ⟨b, hbS, _, hb, _, hbq⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (e.open_target.mem_nhds (e.map_source hqe))
  let v : Plane → Plane := fun x => (1, partialTime h (e.symm x))
  let V : Plane → Plane := fun x => b x • v x
  have hV : ContDiff ℝ ∞ V := smooth_cutoff_mul b v hb (by
    intro x hx
    have hxt := hbS hx
    have hxs := e.map_target hxt
    have ha' := analyticAt_partialTime (hes hxs)
    have hv : AnalyticAt ℝ v x :=
      analyticAt_const.prod (ha'.comp (f := fun x => e.symm x) (heia x hxt))
    exact hv.contDiffAt)
  let U := interior (e.source ∩ {p | b (e p) ≠ 0})
  have hqU : q ∈ U := by
    apply mem_interior_iff_mem_nhds.mpr
    apply inter_mem (e.open_source.mem_nhds hqe)
    have hc := hb.continuous.continuousAt.comp (e.continuousAt hqe)
    exact hc.eventually_ne (by simpa only [Function.comp_apply, hbq] using (one_ne_zero : (1 : ℝ) ≠ 0))
  refine ⟨U, V, isOpen_interior, hqU, hV, ?_⟩
  intro p hp
  have hp' := interior_subset hp
  have hval : V (p.1, h p) = b (e p) • (1, partialTime h p) := by
    change b (G p) • (1, partialTime h (e.symm (G p))) = _
    rw [← he, e.left_inv hp'.1]
  rw [hval]
  constructor
  · intro hz
    have hz' := congrArg Prod.fst hz
    change b (e p) * 1 = 0 at hz'
    exact hp'.2 (by simpa only [mul_one] using hz')
  · simp [Family.wedge]

/-- A countable family of globally smooth fields covers every regular
point of the graph map (t,s) ↦ (t,h(t,s)). -/
theorem exists_countable_smooth_tangents (h : Plane → ℝ) (S : Set Plane)
    (ha : AnalyticOnNhd ℝ h S) :
    ∃ V : Family.Foliations, ∀ p ∈ S, partialParameter h p ≠ 0 →
      ∃ i, V.field i (p.1, h p) ≠ 0 ∧
        Family.wedge (V.field i (p.1, h p)) (1, partialTime h p) = 0 := by
  classical
  let C := {c : Set Plane × (Plane → Plane) // IsOpen c.1 ∧ ContDiff ℝ ∞ c.2 ∧
    ∀ p ∈ c.1, c.2 (p.1, h p) ≠ 0 ∧
      Family.wedge (c.2 (p.1, h p)) (1, partialTime h p) = 0}
  haveI : Nonempty C := ⟨⟨(∅, 0), isOpen_empty, contDiff_const, by simp⟩⟩
  let R := {p | p ∈ S ∧ partialParameter h p ≠ 0}
  have hcover : R ⊆ ⋃ c : C, c.val.1 := by
    intro p hp
    obtain ⟨U, v, hU, hpU, hv, he⟩ := exists_local_smooth_tangent h p (ha p hp.1) hp.2
    exact mem_iUnion.mpr ⟨⟨(U, v), hU, hv, he⟩, hpU⟩
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof R).indexed_countable_subcover
    (fun c : C => c.val.1) (fun c => c.property.1) hcover
  refine ⟨⟨fun i => (f i).val.2, fun i => (f i).property.2.1⟩, ?_⟩
  intro p hp hn
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hf ⟨hp, hn⟩)
  exact ⟨i, (f i).property.2.2 p hi⟩

end PlanarNikodym
