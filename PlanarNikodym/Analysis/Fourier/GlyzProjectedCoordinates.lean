import PlanarNikodym.Analysis.Fourier.GlyzUniformProjectedTorsion
import PlanarNikodym.Analysis.Fourier.GlyzProjectedDerivativeBounds

/-! Actual orthonormal coordinates for the lower-dimensional projected
curve. The torsion and all prescribed finite derivative bounds are
uniform in the separated centers, even though the bases are chosen. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace PlanarNikodym

def glyzOrthogonalCoordinates (l r : ℕ) (t : ℝ) :
    (glyzEuclideanTangentSpace (l + r) r t)ᗮ ≃ₗᵢ[ℝ] GlyzSpace l :=
  ((stdOrthonormalBasis ℝ (glyzEuclideanTangentSpace (l + r) r t)ᗮ).reindex
    (finCongr (finrank_glyzOrthogonalSpace l r t))).repr

def glyzCoordinateCurve (l r : ℕ) (t s : ℝ) : GlyzSpace l :=
  glyzOrthogonalCoordinates l r t (glyzOrthogonalCurve l r t s)

theorem contDiff_glyzCoordinateCurve (l r : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (glyzCoordinateCurve l r t) :=
  (glyzOrthogonalCoordinates l r t).toContinuousLinearEquiv.contDiff.comp
    (contDiff_glyzOrthogonalCurve l r t)

theorem iteratedDeriv_glyzCoordinateCurve (l r n : ℕ) (t s : ℝ) :
    iteratedDeriv n (glyzCoordinateCurve l r t) s =
      glyzOrthogonalCoordinates l r t (iteratedDeriv n (glyzOrthogonalCurve l r t) s) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ n
    ((glyzOrthogonalCoordinates l r t).toContinuousLinearEquiv ∘ glyzOrthogonalCurve l r t) s
      (fun _ => 1) = _
  rw [(glyzOrthogonalCoordinates l r t).toContinuousLinearEquiv.iteratedFDeriv_comp_left]
  rfl

def glyzCoordinateTorsionMatrix (l r : ℕ) (t s : ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  fun k j => iteratedDeriv ((j : ℕ) + 1) (glyzCoordinateCurve l r t) s k

theorem glyzProjectedGram_eq_coordinateGram (l r : ℕ) (s t : ℝ) :
    glyzProjectedGram l r s t = Matrix.gram ℝ
      (fun j : Fin l => iteratedDeriv ((j : ℕ) + 1) (glyzCoordinateCurve l r t) s) := by
  rw [glyzProjectedGram_eq_derivatives]
  ext i j
  simp only [Matrix.gram_apply, iteratedDeriv_glyzCoordinateCurve,
    LinearIsometryEquiv.inner_map_map]

theorem glyz_coordinate_gram_eq (l r : ℕ) (s t : ℝ) :
    glyzProjectedGram l r s t = (glyzCoordinateTorsionMatrix l r t s).transpose *
      glyzCoordinateTorsionMatrix l r t s := by
  rw [glyzProjectedGram_eq_coordinateGram]
  ext i j
  simp [Matrix.gram_apply, glyzCoordinateTorsionMatrix, Matrix.mul_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem abs_det_glyzProjectedGram_eq_sq (l r : ℕ) (s t : ℝ) :
    |(glyzProjectedGram l r s t).det| = |(glyzCoordinateTorsionMatrix l r t s).det| ^ 2 := by
  rw [glyz_coordinate_gram_eq, Matrix.det_mul, Matrix.det_transpose, ← pow_two, abs_pow]

/-- Full geometric certificate for every finite derivative order M:
one positive torsion lower bound and one finite C^M bound work for all
separated centers. The curve and its coordinates are actually built. -/
theorem exists_uniform_glyzCoordinateCurve_certificate (l r M : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧
      (∀ t : ℝ, ContDiff ℝ ∞ (glyzCoordinateCurve l r t)) ∧
      (∀ t : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, ∀ n ≤ M,
        ‖iteratedDeriv n (glyzCoordinateCurve l r t) s‖ ≤ C) ∧
      (∀ z ∈ separatedMixedCenters ν,
        b ≤ |(glyzCoordinateTorsionMatrix l r z.2 z.1).det|) := by
  obtain ⟨β, hβ, ht⟩ := exists_uniform_glyzOrthogonalCurve_torsion l r hν
  obtain ⟨C, hC, hder⟩ := exists_uniform_glyzOrthogonalCurve_derivative_bound l r M
  refine ⟨Real.sqrt β, C, Real.sqrt_pos.mpr hβ, hC, contDiff_glyzCoordinateCurve l r, ?_, ?_⟩
  · intro t s hs n hn
    rw [iteratedDeriv_glyzCoordinateCurve, LinearIsometryEquiv.norm_map]
    exact hder t s hs n hn
  · intro z hz
    have h := ht z hz
    rw [← glyzProjectedGram_eq_derivatives, abs_det_glyzProjectedGram_eq_sq] at h
    nlinarith [Real.sq_sqrt hβ.le, Real.sqrt_nonneg β,
      abs_nonneg ((glyzCoordinateTorsionMatrix l r z.2 z.1).det)]

end PlanarNikodym
