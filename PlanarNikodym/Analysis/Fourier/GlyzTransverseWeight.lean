import PlanarNikodym.Analysis.Fourier.GlyzTransverseCoordinates
import PlanarNikodym.Analysis.Fourier.GlyzCoordinateWeight

/-! Appendix A.2 on the actual orthogonal complement of moment jets.
The constant precedes the center, scale, and physical point. The safe
decay exponent A' = A + (l+r) is used, with r > 0. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem exists_uniform_glyz_transverse_weight (l r A : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ x : GlyzSpace (l + r),
      glyzSubspaceAverage
        (glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t) (A + (l + r)) (δ ^ (r + 1)))
        (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL
        (fun y => ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame (l + r) t δ hδ) y)) x ≤
      ENNReal.ofReal C * ENNReal.ofReal
        (glyzPolarWeight A (glyzMomentFrequencyFrame (l + r) t δ hδ) x) := by
  obtain ⟨D, hD, hcoords⟩ := exists_uniform_glyzTransverse_coordinates l r
  let C := (2 * D) ^ A * ∫ z : Base l, glyzDecayWeight (l + r) z
  have hD0 : 0 < D := by linarith
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (integral_nonneg fun z => (glyzDecayWeight_pos _ z).le)
  refine ⟨C + 1, by linarith, ?_⟩
  intro t ht δ hδ hδ1 x
  rw [glyzCoordinateMeasure_average _ _ _ _
    (continuous_glyzPolarWeight A _).measurable.ennreal_ofReal]
  have h := lintegral_glyzPolarWeight_subspace_le A (show l < l + r by omega)
    (glyzMomentFrequencyFrame (l + r) t δ hδ) (glyzTransverseParameterization l r t)
    hD (pow_pos hδ (r + 1)) (hcoords t ht δ hδ hδ1) x
  apply h.trans
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : C ≤ C + 1)) le_rfl

end PlanarNikodym
