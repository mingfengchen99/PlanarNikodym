import PlanarNikodym.Analysis.Fourier.GlyzProjectedSlice
import PlanarNikodym.Analysis.Fourier.GlyzProjectedCurveNesting
import PlanarNikodym.Analysis.Fourier.GlyzSchwartzTranslation
import PlanarNikodym.Analysis.Fourier.GlyzCoordinateWeight

/-! Actual affine slices through any ambient point, their Fourier
support, and exact transport of the transverse ball and coordinate
averages to Euclidean coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

def glyzProjectedSliceAt (l r : ℕ) (t : ℝ) (x : GlyzSpace (l + r))
    (f : SchwartzMap (GlyzSpace (l + r)) ℂ) : SchwartzMap (GlyzSpace l) ℂ :=
  glyzProjectedSlice l r t (glyzSchwartzTranslate x f) 0

theorem glyzProjectedSliceAt_apply (l r : ℕ) (t : ℝ) (x : GlyzSpace (l + r))
    (f : SchwartzMap (GlyzSpace (l + r)) ℂ) (y : GlyzSpace l) :
    glyzProjectedSliceAt l r t x f y =
      f (x + ((glyzOrthogonalCoordinates l r t).symm y : GlyzSpace (l + r))) := by
  simp only [glyzProjectedSliceAt, glyzProjectedSlice_apply, glyzSchwartzTranslate_apply,
    Submodule.coe_zero, zero_add, add_comm]

theorem glyzProjectedSliceAt_sum {ι : Type*} (l r : ℕ) (t : ℝ)
    (x : GlyzSpace (l + r)) (I : Finset ι) (f : ι → SchwartzMap (GlyzSpace (l + r)) ℂ) :
    glyzProjectedSliceAt l r t x (∑ i ∈ I, f i) =
      ∑ i ∈ I, glyzProjectedSliceAt l r t x (f i) := by
  ext y
  simp only [glyzProjectedSliceAt_apply, sum_apply]

theorem glyzProjectedSlice_fourier_support_enlarged (l r : ℕ) (t s δ R : ℝ) (hδ : 0 < δ)
    (f : SchwartzMap (GlyzSpace (l + r)) ℂ) (z : (glyzEuclideanTangentSpace (l + r) r t)ᗮᗮ)
    (hsupp : Function.support (𝓕 (f : GlyzSpace (l + r) → ℂ)) ⊆
      glyzFrequencyBox (glyzMomentFrequencyFrame (l + r) s δ hδ)
        ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) s)) R) :
    Function.support (𝓕 (glyzProjectedSlice l r t f z : GlyzSpace l → ℂ)) ⊆
      glyzCoordinateProjection l r t ''
        glyzFrequencyBox (glyzMomentFrequencyFrame (l + r) s δ hδ)
          ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) s)) R := by
  let K := (glyzEuclideanTangentSpace (l + r) r t)ᗮ
  let e := glyzOrthogonalCoordinates l r t
  have hs := glyzSubspaceSlice_fourier_support K f z (isCompact_glyzFrequencyBox _ _ _) hsupp
  intro ξ hξ
  have hh : 𝓕 (glyzSubspaceSlice K f z : K → ℂ) (e.symm ξ) ≠ 0 := by
    change 𝓕 ((glyzSubspaceSlice K f z : K → ℂ) ∘ e.symm) ξ ≠ 0 at hξ
    rwa [Real.fourier_comp_linearIsometry] at hξ
  obtain ⟨η, hη, he⟩ := hs hh
  refine ⟨η, hη, ?_⟩
  change e (K.orthogonalProjectionOnto η) = ξ
  rw [he, e.apply_symm_apply]

/-- Every actual affine slice has the uniformly enlarged projected
curve support, for arbitrary fixed ambient radius. -/
theorem exists_uniform_glyzProjectedSliceAt_support (l r : ℕ)
    {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ u ∈ separatedMixedCenters ν,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      ∀ (f : SchwartzMap (GlyzSpace (l + r)) ℂ) (x : GlyzSpace (l + r)),
      Function.support (𝓕 (f : GlyzSpace (l + r) → ℂ)) ⊆
        glyzFrequencyBox (glyzMomentFrequencyFrame (l + r) u.1 δ hδ)
          ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm (glyzMomentCurve (l + r) u.1)) R →
      Function.support (𝓕 (glyzProjectedSliceAt l r u.2 x f : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r u.2) l u.1 δ Q := by
  obtain ⟨Q, hQ, hproj⟩ := exists_uniform_glyz_projected_enlarged_frequencyBox l r hν hR
  refine ⟨Q, hQ, fun u hu δ hδ hδ1 f x hf => ?_⟩
  exact (glyzProjectedSlice_fourier_support_enlarged l r u.2 u.1 δ R hδ
    (glyzSchwartzTranslate x f) 0 (by rwa [support_fourier_glyzSchwartzTranslate])).trans
      (hproj u hu δ hδ hδ1)

section Transport
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyzBallMeasure_lintegral_isometry (e : H ≃ₗᵢ[ℝ] E) (R : ℝ) (F : E → ℝ≥0∞) :
    (∫⁻ z, F (e z) ∂glyzBallMeasure H R) =
      ∫⁻ y, F y ∂glyzBallMeasure E R := by
  have hpre : e ⁻¹' closedBall (0 : E) R = closedBall (0 : H) R := by
    ext z
    simp only [mem_preimage, mem_closedBall, dist_zero_right, e.norm_map]
  have hvol : volume (closedBall (0 : H) R) = volume (closedBall (0 : E) R) := by
    have h := congrArg (fun μ : Measure E => μ (closedBall (0 : E) R)) e.measurePreserving.map_eq
    rwa [Measure.map_apply e.continuous.measurable measurableSet_closedBall, hpre] at h
  have hint := e.measurePreserving.setLIntegral_comp_preimage_emb
    e.toHomeomorph.measurableEmbedding F (closedBall (0 : E) R)
  rw [hpre] at hint
  simp only [glyzBallMeasure, lintegral_smul_measure, smul_eq_mul, hvol, hint]

theorem glyzCoordinateMeasure_lintegral {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l)
    (A : ℕ) (b : ℝ) {F : GlyzSpace l → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F (e z) ∂glyzCoordinateMeasure e A b) =
      ∫⁻ y, F y * ENNReal.ofReal
        (glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) y)) := by
  have hf : Measurable (fun z => F (e z)) := hF.comp e.continuous.measurable
  rw [glyzCoordinateMeasure, lintegral_withDensity_eq_lintegral_mul volume
    (continuous_glyzCoordinateWeight e A b).measurable.ennreal_ofReal
      hf]
  have h := e.measurePreserving.lintegral_comp_emb e.toHomeomorph.measurableEmbedding
    (fun y => F y * ENNReal.ofReal (glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) y)))
  simpa only [glyzCoordinateWeight, Pi.mul_apply, mul_comm] using h

theorem glyzCoordinateMeasure_neg_isometry {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l)
    (A : ℕ) (b : ℝ) :
    glyzCoordinateMeasure (e.trans (LinearIsometryEquiv.neg ℝ)) A b =
      glyzCoordinateMeasure e A b := by
  unfold glyzCoordinateMeasure glyzCoordinateWeight glyzIsotropicWeight glyzDecayWeight
  congr 1
  ext z
  simp
end Transport

theorem glyzProjectedSliceAt_ball_average (l r : ℕ) (t : ℝ) (x : GlyzSpace (l + r))
    (f : SchwartzMap (GlyzSpace (l + r)) ℂ) (p R : ℝ) :
    (∫⁻ y, ‖glyzProjectedSliceAt l r t x f y‖ₑ ^ p ∂glyzBallMeasure (GlyzSpace l) R) =
      glyzSubspaceAverage
        (glyzBallMeasure ((glyzEuclideanTangentSpace (l + r) r t)ᗮ) R)
        (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL (fun y => ‖f y‖ₑ ^ p) x := by
  let e := (glyzOrthogonalCoordinates l r t).trans (LinearIsometryEquiv.neg ℝ)
  rw [← glyzBallMeasure_lintegral_isometry e]
  unfold glyzSubspaceAverage
  apply lintegral_congr
  intro z
  simp [e, glyzProjectedSliceAt_apply, sub_eq_add_neg]

theorem glyzProjectedSliceAt_coordinate_average (l r A : ℕ) (t b p : ℝ)
    (x : GlyzSpace (l + r)) (f : SchwartzMap (GlyzSpace (l + r)) ℂ) :
    (∫⁻ y, ‖glyzProjectedSliceAt l r t x f y‖ₑ ^ p * ENNReal.ofReal
      (glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) y))) =
      glyzSubspaceAverage (glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t) A b)
        (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL (fun y => ‖f y‖ₑ ^ p) x := by
  let e := (glyzOrthogonalCoordinates l r t).trans (LinearIsometryEquiv.neg ℝ)
  rw [← glyzCoordinateMeasure_lintegral e A b
    ((glyzProjectedSliceAt l r t x f).continuous.measurable.enorm.pow_const p)]
  rw [glyzCoordinateMeasure_neg_isometry]
  unfold glyzSubspaceAverage
  apply lintegral_congr
  intro z
  simp [e, glyzProjectedSliceAt_apply, sub_eq_add_neg]

end PlanarNikodym
