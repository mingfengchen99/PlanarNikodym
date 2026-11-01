import PlanarNikodym.Analysis.Fourier.GlyzControlledCurveLocalization
import PlanarNikodym.Analysis.Fourier.GlyzSchwartzTranslation

/-! The controlled-curve local estimate at every physical center.
Spatial translation preserves each actual Fourier support and moves the
decaying weight along with the ball. All constants are independent of
the physical center. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

/-- Corollary 3.7 for the actual projected curves on a ball about any
physical center, from the ordinary lower-dimensional moment theorem. -/
theorem glyz_controlled_curve_translated_local_of_moment_optimal_zero
    (l r A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0)
    {ν Q ε : ℝ} (hν : 0 < ν) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (a : GlyzSpace l),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall a ((glyzDyadicScale N ^ l)⁻¹),
        ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A ((glyzDyadicScale N ^ l) • (x - a)))) ^
              (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_controlled_curve_weighted_local_of_moment_optimal_zero
    l r A hp hη hν hQ hε
  refine ⟨C, hC, fun N t I f a hI hsep hf => ?_⟩
  have h := hlocal N t I (fun j => glyzSchwartzTranslate a (f j)) hI hsep (by
    intro j hj
    rw [support_fourier_glyzSchwartzTranslate]
    exact hf j hj)
  rw [← glyzSchwartzTranslate_sum] at h
  simp_rw [glyz_lintegral_schwartz_translate_weight] at h
  simp only [glyzSchwartzTranslate_apply] at h
  rw [glyz_lintegral_closedBall_translate a ((glyzDyadicScale N ^ l)⁻¹)
    (fun x => ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ))] at h
  exact h

/-- Volume-normalized version on any physical ball. The translated
weight is normalized by the volume of that same ball. -/
theorem glyz_controlled_curve_translated_normalized_local_of_moment_optimal_zero
    (l r A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0)
    {ν Q ε : ℝ} (hν : 0 < ν) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (a : GlyzSpace l),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x, ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)
        ∂glyzCenteredBallMeasure a ((glyzDyadicScale N ^ l)⁻¹)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ((volume (closedBall a ((glyzDyadicScale N ^ l)⁻¹)))⁻¹ *
              ENNReal.ofReal (glyzNormWeight A ((glyzDyadicScale N ^ l) • (x - a))))) ^
                (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_controlled_curve_translated_local_of_moment_optimal_zero
    l r A hp hη hν hQ hε
  refine ⟨C, hC, fun N t I f a hI hsep hf => ?_⟩
  exact glyz_normalize_centered_local_decoupling I f a
    (by positivity [glyzDyadicScale_pos N])
    (by exact_mod_cast lt_of_lt_of_le zero_lt_one hp) _ _
    (hlocal N t I f a hI hsep hf)

end PlanarNikodym
