import PlanarNikodym.Geometry.AnalyticFiniteOrder
import PlanarNikodym.Avoidance.RegularLevelNullity

/-! Nullity of all zeroes of a nontrivial real analytic function, including
singular zeroes. Arbitrary ambient extensions outside the open analytic
domain are allowed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology

namespace PlanarNikodym

theorem regular_coordinate_zero_set_null_on_open {n : ℕ}
    (f : Base (n + 1) → ℝ) {W : Set (Base (n + 1))}
    (ho : IsOpen W) (hf : ContinuousOn f W) (j : Fin (n + 1)) :
    volume {x | x ∈ W ∧ f x = 0 ∧
      fderiv ℝ f x (Pi.single j 1) ≠ 0} = 0 := by
  classical
  let F := W.piecewise f (fun _ => (0 : ℝ))
  have hF : Measurable F :=
    hf.measurable_piecewise continuousOn_const ho.measurableSet
  apply measure_mono_null (t := {x | F x = 0 ∧
    fderiv ℝ F x (Pi.single j 1) ≠ 0})
  · intro x hx
    have he : F =ᶠ[𝓝 x] f := by
      filter_upwards [ho.mem_nhds hx.1] with y hy
      exact piecewise_eq_of_mem W f (fun _ => 0) hy
    refine ⟨?_, ?_⟩
    · exact (he.self_of_nhds).trans hx.2.1
    · rw [he.fderiv_eq (𝕜 := ℝ)]
      exact hx.2.2
  · exact regular_coordinate_zero_set_null F hF j

/-- Real analytic zero sets have zero ambient volume without a
first-order regularity assumption. This is not a statement about a
lower-dimensional projection of that zero set. -/
theorem analytic_zero_set_null {n : ℕ} {f : Base (n + 1) → ℝ}
    {W : Set (Base (n + 1))} (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (hc : IsPreconnected W) (hne : ∃ q ∈ W, f q ≠ 0) :
    volume {x | x ∈ W ∧ f x = 0} = 0 := by
  apply measure_mono_null (analytic_zero_set_subset_regular_coordinateJets ha hc hne)
  apply measure_iUnion_null
  intro k
  apply measure_iUnion_null
  intro s
  apply measure_iUnion_null
  intro j
  exact regular_coordinate_zero_set_null_on_open (coordinateJet f k s) ho
    (coordinateJet_analytic ha k s).continuousOn j

theorem compact_analytic_zero_set_closed_null {n : ℕ} {f : Base (n + 1) → ℝ}
    {W K : Set (Base (n + 1))} (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (hc : IsPreconnected W) (hne : ∃ q ∈ W, f q ≠ 0)
    (hK : IsCompact K) (hKW : K ⊆ W) :
    IsClosed {x | x ∈ K ∧ f x = 0} ∧ volume {x | x ∈ K ∧ f x = 0} = 0 := by
  have hsub : {x | x ∈ K ∧ f x = 0} ⊆ {x | x ∈ W ∧ f x = 0} :=
    fun _ hx => ⟨hKW hx.1, hx.2⟩
  refine ⟨?_, measure_mono_null hsub (analytic_zero_set_null ho ha hc hne)⟩
  exact (ha.continuousOn.mono hKW).preimage_isClosed_of_isClosed
    hK.isClosed isClosed_singleton

/-- Compact containment inside the analytic domain justifies closure
nullity even for singular zeroes. -/
theorem closure_analytic_zeros_null_of_compact_container {n : ℕ}
    {f : Base (n + 1) → ℝ} {W K S : Set (Base (n + 1))}
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W) (hc : IsPreconnected W)
    (hne : ∃ q ∈ W, f q ≠ 0) (hK : IsCompact K) (hKW : K ⊆ W)
    (hSK : S ⊆ K) (hzero : ∀ x ∈ S, f x = 0) :
    volume (closure S) = 0 := by
  obtain ⟨hclosed, hnull⟩ := compact_analytic_zero_set_closed_null ho ha hc hne hK hKW
  exact measure_mono_null
    (hclosed.closure_subset_iff.mpr (fun x hx => ⟨hSK hx, hzero x hx⟩)) hnull

end PlanarNikodym
