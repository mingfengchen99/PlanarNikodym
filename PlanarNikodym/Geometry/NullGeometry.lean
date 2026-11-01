import PlanarNikodym.Geometry.RankTransport
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

instance planeVolumeHaar : Measure.IsAddHaarMeasure (volume : Measure Plane) := by
  change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure ℝ))
  infer_instance

instance baseTwoVolumeHaar : Measure.IsAddHaarMeasure (volume : Measure (Base 2)) :=
  isAddHaarMeasure_volume_pi (Fin 2)

theorem null_of_locally_null {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) (S : Set X)
    (h : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ (S ∩ U) = 0) : μ S = 0 := by
  classical
  choose U hU using h
  obtain ⟨T, hTc, hT⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    (fun x : S => U x x.property) (fun x => (hU x x.property).1) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, (hU x hx).2.1⟩)
  haveI := hTc.to_subtype
  apply measure_mono_null (t := ⋃ x : T, S ∩ U x.val x.val.property)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hT hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx, hxi⟩
  · exact measure_iUnion_null (fun x => (hU x.val x.val.property).2.2)

theorem analytic_chart_preimage_null {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (e : OpenPartialHomeomorph E E) (hi : AnalyticOnNhd ℝ e.symm e.target)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (A : Set E) (hA : μ A = 0) :
    μ (e.source ∩ e ⁻¹' A) = 0 := by
  have he : e.source ∩ e ⁻¹' A = e.symm '' (e.target ∩ A) := by
    ext x
    constructor
    · rintro ⟨hx, ha⟩
      exact ⟨e x, ⟨e.map_source hx, ha⟩, e.left_inv hx⟩
    · rintro ⟨y, ⟨hy, ha⟩, rfl⟩
      refine ⟨e.map_target hy, ?_⟩
      change e (e.symm y) ∈ A
      rwa [e.right_inv hy]
  rw [he]
  apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := μ) (fun y hy => (hi y hy.1).differentiableAt.differentiableWithinAt)
  exact measure_mono_null inter_subset_right hA

/-- Null pullback on the regular locus, without any measurability hypothesis
on the target set. The countable gluing uses second countability. -/
theorem analytic_regular_preimage_null {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] (f : E → E) (U : Set E)
    (hf : AnalyticOnNhd ℝ f U) (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (A : Set E) (hA : μ A = 0) :
    μ {x | x ∈ U ∧ (fderiv ℝ f x).IsInvertible ∧ f x ∈ A} = 0 := by
  apply null_of_locally_null μ
  intro x hx
  obtain ⟨e, hxe, _, he, _, hei⟩ := exists_analytic_chart f x (hf x hx.1) hx.2.1 univ (by simp)
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  apply measure_mono_null (t := e.source ∩ e ⁻¹' A)
  · rintro y ⟨⟨_, _, hy⟩, hys⟩
    refine ⟨hys, ?_⟩
    change e y ∈ A
    rwa [he]
  · exact analytic_chart_preimage_null e hei μ A hA

end PlanarNikodym
