import PlanarNikodym.Analysis.Fourier.GlyzWeightedConvolution
import PlanarNikodym.Analysis.Fourier.GlyzLocalAverage

/-! Local constancy of the actual convolved second factor on the
transverse balls at the scale required by Lemma 3.8. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

/-- A pointwise shift bound propagates through positive convolution. -/
theorem glyzPositiveConvolution_shift {m : ℕ} {F w : GlyzSpace m → ℝ≥0∞}
    (v : GlyzSpace m) (C : ℝ≥0∞) (hC : C ≠ ⊤) (hw : ∀ x, w (x - v) ≤ C * w x)
    (x : GlyzSpace m) : glyzPositiveConvolution F w (x - v) ≤ C * glyzPositiveConvolution F w x := by
  unfold glyzPositiveConvolution
  calc
    _ ≤ ∫⁻ y, C * (F y * w (x - y)) := by
      apply lintegral_mono
      intro y
      have he : x - v - y = x - y - v := by abel
      dsimp only
      rw [he]
      exact (mul_le_mul' le_rfl (hw (x - y))).trans_eq (by ring)
    _ = _ := lintegral_const_mul' _ _ hC

/-- Local constancy on an arbitrary polar box, propagated to its
Schwartz power average. -/
theorem glyzPolarPowerAverage_shift {m : ℕ} (A : ℕ)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (g : SchwartzMap (GlyzSpace m) ℂ)
    (q : ℝ) (z : GlyzSpace m) {D : ℝ} (hD : 1 ≤ D)
    (hcoord : ‖glyzBoxCoordinates L z‖ ≤ D) (x : GlyzSpace m) :
    glyzPowerAverage (glyzPolarMeasure A L) g q (x - z) ≤
      ENNReal.ofReal ((2 * D) ^ A) * glyzPowerAverage (glyzPolarMeasure A L) g q x := by
  have hw (y : GlyzSpace m) :
      ENNReal.ofReal (glyzPolarWeight A L (y - z)) ≤
        ENNReal.ofReal ((2 * D) ^ A) * ENNReal.ofReal (glyzPolarWeight A L y) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * D) ^ A)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ 2 ^ A * glyzPolarWeight A L y * max (1 : ℝ) ‖glyzBoxCoordinates L z‖ ^ A :=
        glyzPolarWeight_shift A L y z
      _ ≤ 2 ^ A * glyzPolarWeight A L y * D ^ A :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (max_le hD hcoord) A)
            (mul_nonneg (by positivity) (glyzPolarWeight_pos A L y).le)
      _ = _ := by rw [mul_pow]; ring
  rw [glyzPolarMeasure_powerAverage_eq_convolution, glyzPolarMeasure_powerAverage_eq_convolution]
  exact glyzPositiveConvolution_shift z _ ENNReal.ofReal_ne_top hw x

/-- The constant depends only on dimension and decay order, and is
uniform over all functions, powers, centers, scales, and ball points. -/
theorem exists_uniform_glyz_transverse_powerAverage_shift (l r A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ (g : SchwartzMap (GlyzSpace (l + r)) ℂ) (q : ℝ),
      ∀ z : (glyzEuclideanTangentSpace (l + r) r t)ᗮ,
      ‖z‖ ≤ (δ ^ (r + 1))⁻¹ → ∀ x : GlyzSpace (l + r),
      glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ))
        g q (x - z) ≤ ENNReal.ofReal C *
      glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q x := by
  obtain ⟨D, hD, hjet⟩ := exists_uniform_glyzEuclideanJet_bound (l + r)
  refine ⟨(2 * D) ^ A, pow_pos (by linarith) A, ?_⟩
  intro t ht δ hδ hδ1 g q z hz x
  let L := glyzMomentFrequencyFrame (l + r) t δ hδ
  have hcoord : ‖glyzBoxCoordinates L z‖ ≤ D := by
    have h := glyzMomentCoordinates_transverse_bound (by linarith : 0 ≤ D)
      (hjet t ht) hδ hδ1 z
    apply h.trans
    calc
      _ ≤ D * δ ^ (r + 1) * (δ ^ (r + 1))⁻¹ :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      _ = D := by rw [mul_assoc, mul_inv_cancel₀ (pow_pos hδ _).ne', mul_one]
  exact glyzPolarPowerAverage_shift A L g q (z : GlyzSpace (l + r)) hD hcoord x

/-- The first local-averaging step of Lemma 3.8 for the actual polar
Schwartz factor and the actual orthogonal-complement ball. -/
theorem exists_uniform_glyz_transverse_localize (l r A : ℕ) (hA : l + r < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ (g : SchwartzMap (GlyzSpace (l + r)) ℂ) (q : ℝ)
      (F : GlyzSpace (l + r) → ℝ≥0∞), Measurable F →
      let G := glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q
      (∫⁻ x, F x * G x) ≤ ENNReal.ofReal C *
        ∫⁻ x, glyzSubspaceAverage
          (glyzBallMeasure ((glyzEuclideanTangentSpace (l + r) r t)ᗮ) ((δ ^ (r + 1))⁻¹))
          (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL F x * G x := by
  obtain ⟨C, hC, hshift⟩ := exists_uniform_glyz_transverse_powerAverage_shift l r A
  refine ⟨C, hC, ?_⟩
  intro t ht δ hδ hδ1 g q F hF
  letI := isFiniteMeasure_glyzPolarMeasure hA (glyzMomentFrequencyFrame (l + r) t δ hδ)
  letI := isProbabilityMeasure_glyzBallMeasure
    (H := (glyzEuclideanTangentSpace (l + r) r t)ᗮ) (inv_pos.mpr (pow_pos hδ (r + 1)))
  exact glyz_localize_bilinear _ _ hF (measurable_glyzPowerAverage _ g q)
    (ENNReal.ofReal C) ENNReal.ofReal_ne_top fun x =>
      (ae_glyzBallMeasure_norm_le ((δ ^ (r + 1))⁻¹)).mono fun z hz =>
        hshift t ht δ hδ hδ1 g q z hz x

end PlanarNikodym
