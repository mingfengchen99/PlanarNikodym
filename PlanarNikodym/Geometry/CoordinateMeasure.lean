import PlanarNikodym.Geometry.NullGeometry
import PlanarNikodym.Core.ReuseBasics
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open Set Filter MeasureTheory Module
open scoped Topology NNReal ENNReal
namespace PlanarNikodym

theorem linearEquiv_image_null {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    (e : E ≃L[ℝ] F) (μ : Measure E) (ν : Measure F)
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    (A : Set E) (hA : μ A = 0) : ν (e '' A) = 0 := by
  have hac : ν ≪ μ.map e := Measure.absolutelyContinuous_isAddHaarMeasure ν (μ.map e)
  apply hac
  change (μ.map (e.toHomeomorph : E → F)) (e.toHomeomorph '' A) = 0
  rw [e.toHomeomorph.measurableEmbedding.map_apply,
    Set.preimage_image_eq _ e.toHomeomorph.injective]
  exact hA

theorem analytic_image_null_coordinates (K : Plane ≃L[ℝ] Base 2) (f : Plane → Plane)
    (U : Set Plane) (hf : AnalyticOnNhd ℝ f U) (A : Set Plane) (hAU : A ⊆ U)
    (hA : volume A = 0) : volume ((fun p => K (f p)) '' A) = 0 := by
  have hi : volume (f '' A) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume)
      (fun p hp => (hf p (hAU hp)).differentiableAt.differentiableWithinAt) hA
  rw [← Set.image_image]
  exact linearEquiv_image_null K volume volume _ hi

theorem positive_part_of_curve_left_inverse {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (ψ : ℝ → E) (P : E → ℝ)
    {K : ℝ≥0} (hP : LipschitzWith K P) {l r : ℝ} (hlr : l < r)
    (hc : ContinuousOn ψ (Icc l r)) (he : ∀ t ∈ Icc l r, P (ψ t) = t) :
    HasPositivePart (Measure.hausdorffMeasure 1) (ψ '' Icc l r) := by
  have hm := (isCompact_Icc.image_of_continuousOn hc).measurableSet
  refine ⟨ψ '' Icc l r, Subset.rfl, hm, ?_⟩
  apply pos_iff_ne_zero.mpr
  intro hz
  have him : P '' (ψ '' Icc l r) = Icc l r := by
    ext t
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      rwa [he s hs]
    · intro ht
      exact ⟨ψ t, ⟨t, ht, rfl⟩, he t ht⟩
  have hle := hP.hausdorffMeasure_image_le (d := 1) (by norm_num) (ψ '' Icc l r)
  rw [him, hausdorffMeasure_real, Real.volume_Icc, hz] at hle
  have hp : 0 < ENNReal.ofReal (r - l) := ENNReal.ofReal_pos.mpr (sub_pos.mpr hlr)
  exact hp.not_ge (by simpa using hle)

end PlanarNikodym
