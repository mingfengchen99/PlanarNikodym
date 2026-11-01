import PlanarNikodym.Analysis.Fourier.GlyzProjectedFrequencyBox

/-! Every affine orthogonal slice, in actual orthonormal coordinates,
has Fourier support in a uniformly enlarged lower-dimensional curve box. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform Real
open scoped FourierTransform
namespace PlanarNikodym

def glyzProjectedSlice (l r : ℕ) (t : ℝ) (f : SchwartzMap (GlyzSpace (l + r)) ℂ)
    (z : (glyzEuclideanTangentSpace (l + r) r t)ᗮᗮ) : SchwartzMap (GlyzSpace l) ℂ :=
  (glyzSubspaceSlice (glyzEuclideanTangentSpace (l + r) r t)ᗮ f z).compCLMOfContinuousLinearEquiv ℂ
    (glyzOrthogonalCoordinates l r t).symm.toContinuousLinearEquiv

theorem glyzProjectedSlice_apply (l r : ℕ) (t : ℝ) (f : SchwartzMap (GlyzSpace (l + r)) ℂ)
    (z : (glyzEuclideanTangentSpace (l + r) r t)ᗮᗮ) (x : GlyzSpace l) :
    glyzProjectedSlice l r t f z x =
      f (((glyzOrthogonalCoordinates l r t).symm x : GlyzSpace (l + r)) + z) := by
  change glyzSubspaceSlice (glyzEuclideanTangentSpace (l + r) r t)ᗮ f z
    ((glyzOrthogonalCoordinates l r t).symm x) = _
  exact glyzSubspaceSlice_apply _ _ _ _

theorem glyzProjectedSlice_fourier_support (l r : ℕ) (t s δ : ℝ) (hδ : 0 < δ)
    (f : SchwartzMap (GlyzSpace (l + r)) ℂ) (z : (glyzEuclideanTangentSpace (l + r) r t)ᗮᗮ)
    (hsupp : Function.support (𝓕 (f : GlyzSpace (l + r) → ℂ)) ⊆ glyzMomentFrequencyBox (l + r) s δ hδ) :
    Function.support (𝓕 (glyzProjectedSlice l r t f z : GlyzSpace l → ℂ)) ⊆
      glyzCoordinateProjection l r t '' glyzMomentFrequencyBox (l + r) s δ hδ := by
  let K := (glyzEuclideanTangentSpace (l + r) r t)ᗮ
  let e := glyzOrthogonalCoordinates l r t
  have hs := glyzMoment_subspace_slice_support (l + r) s δ hδ K f z hsupp
  intro ξ hξ
  have hh : 𝓕 (glyzSubspaceSlice K f z : K → ℂ) (e.symm ξ) ≠ 0 := by
    change 𝓕 ((glyzSubspaceSlice K f z : K → ℂ) ∘ e.symm) ξ ≠ 0 at hξ
    rwa [fourier_comp_linearIsometry] at hξ
  obtain ⟨η, hη, he⟩ := hs hh
  refine ⟨η, hη, ?_⟩
  change e (K.orthogonalProjectionOnto η) = ξ
  rw [he, e.apply_symm_apply]

/-- Uniform Fourier support certificate for every actual affine slice
in the lower-degree step. The constant is independent of the original
Schwartz function, translation, separated centers, and scale. -/
theorem exists_uniform_glyzProjectedSlice_support (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ R : ℝ, 0 < R ∧ ∀ u ∈ separatedMixedCenters ν,
      ∃ L : GlyzSpace l ≃L[ℝ] GlyzSpace l,
        L.toContinuousLinearMap = glyzCurveJetOperator (glyzCoordinateCurve l r u.2) u.1 ∧
        ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
        ∀ (f : SchwartzMap (GlyzSpace (l + r)) ℂ)
          (z : (glyzEuclideanTangentSpace (l + r) r u.2)ᗮᗮ),
        Function.support (𝓕 (f : GlyzSpace (l + r) → ℂ)) ⊆ glyzMomentFrequencyBox (l + r) u.1 δ hδ →
        Function.support (𝓕 (glyzProjectedSlice l r u.2 f z : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzScaledFrame L δ hδ) (glyzCoordinateCurve l r u.2 u.1) R := by
  obtain ⟨R, hR, hbox⟩ := exists_uniform_glyz_projected_frequencyBox l r hν
  refine ⟨R, hR, ?_⟩
  intro u hu
  obtain ⟨L, hL, hinc⟩ := hbox u hu
  refine ⟨L, hL, ?_⟩
  intro δ hδ hδ1 f z hsupp
  exact (glyzProjectedSlice_fourier_support l r u.2 u.1 δ hδ f z hsupp).trans (hinc δ hδ hδ1)

end PlanarNikodym
