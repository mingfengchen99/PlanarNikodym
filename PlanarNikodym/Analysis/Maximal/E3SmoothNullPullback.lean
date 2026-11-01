import PlanarNikodym.Analysis.Fourier.GlyzSmoothJetCoordinates
import PlanarNikodym.Geometry.NullGeometry

/-! The regular-locus null-pullback argument needs genuine smooth inverse
charts, and does not require analytic zero-set arguments. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PlanarNikodym

theorem e3_smooth_chart_preimage_null {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : OpenPartialHomeomorph E E)
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x)
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
    (μ := μ) (fun y hy => ((hi y hy.1).differentiableAt (by simp)).differentiableWithinAt)
  exact measure_mono_null inter_subset_right hA

theorem e3_smooth_regular_preimage_null {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E → E) (hf : ContDiff ℝ ∞ f) (U : Set E)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (A : Set E) (hA : μ A = 0) :
    μ {x | x ∈ U ∧ (fderiv ℝ f x).IsInvertible ∧ f x ∈ A} = 0 := by
  apply null_of_locally_null μ
  intro x hx
  obtain ⟨e, hxe, _, he, _, hei⟩ :=
    exists_glyz_smooth_chart f hf x hx.2.1 univ (by simp)
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  apply measure_mono_null (t := e.source ∩ e ⁻¹' A)
  · rintro y ⟨⟨_, _, hy⟩, hys⟩
    refine ⟨hys, ?_⟩
    change e y ∈ A
    rwa [he]
  · exact e3_smooth_chart_preimage_null e hei μ A hA

end PlanarNikodym
