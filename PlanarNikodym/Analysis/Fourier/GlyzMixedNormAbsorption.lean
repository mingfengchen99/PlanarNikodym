import PlanarNikodym.Analysis.Fourier.GlyzMixedNorm
import PlanarNikodym.Analysis.Fourier.GlyzWeightedConvolution

/-! The integrated mixed-norm and transverse-weight absorption step
of Lemma 3.8, including its actual moment-curve specialization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace PlanarNikodym

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

theorem glyz_weighted_mixed_l2_absorb {ι : Type*} (s : Finset ι)
    (μ : Measure H) [SFinite μ] [Measure.IsNegInvariant μ] (S : H →L[ℝ] E)
    (F : ι → E → ℝ≥0∞) (G : E → ℝ≥0∞)
    (hF : ∀ i ∈ s, Measurable (F i)) (hG : Measurable G)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hstable : ∀ x, glyzSubspaceAverage μ S G x ≤ C * G x)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫⁻ x, G x * (∑ i ∈ s, glyzSubspaceAverage μ S (F i) x ^ (2 / p)) ^ (p / 2)) ≤
      C * (∑ i ∈ s, (∫⁻ x, G x * F i x) ^ (2 / p)) ^ (p / 2) := by
  have hp0 : 0 < p := by linarith
  have hpair (i : ι) (hi : i ∈ s) :
      (∫⁻ x, G x * glyzSubspaceAverage μ S (F i) x) ≤ C * ∫⁻ x, G x * F i x := by
    simpa only [mul_comm] using glyzSubspaceAverage_pairing_le μ S (hF i hi) hG C hC hstable
  calc
    _ ≤ (∑ i ∈ s, (∫⁻ x, G x * glyzSubspaceAverage μ S (F i) x) ^ (2 / p)) ^ (p / 2) :=
      glyz_lintegral_weighted_mixed_l2 volume s G _ hG
        (fun i hi => measurable_glyzSubspaceAverage μ S (hF i hi)) hp
    _ ≤ (∑ i ∈ s, (C * ∫⁻ x, G x * F i x) ^ (2 / p)) ^ (p / 2) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact Finset.sum_le_sum fun i hi => ENNReal.rpow_le_rpow (hpair i hi) (by positivity)
    _ = _ := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 2 / p)]
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ p / 2),
        ← ENNReal.rpow_mul, show 2 / p * (p / 2) = 1 by field_simp, ENNReal.rpow_one]

/-- A genuine uniform estimate for the actual weights and second
Schwartz factor in Lemma 3.8. The first family can consist of arbitrary
measurable nonnegative convolutions. No decoupling gain is assumed. -/
theorem exists_uniform_glyz_transverse_mixed_l2 (l r A : ℕ) (hr : 0 < r) (hA : l + r < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ (g : SchwartzMap (GlyzSpace (l + r)) ℂ) (q : ℝ),
      ∀ (ι : Type) (s : Finset ι) (F : ι → GlyzSpace (l + r) → ℝ≥0∞),
      (∀ i ∈ s, Measurable (F i)) → ∀ p : ℝ, 2 ≤ p →
      let G := glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q
      let μ := glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t) (A + (l + r)) (δ ^ (r + 1))
      (∫⁻ x, G x * (∑ i ∈ s, glyzSubspaceAverage μ
        (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL (F i) x ^ (2 / p)) ^ (p / 2)) ≤
      ENNReal.ofReal C * (∑ i ∈ s, (∫⁻ x, G x * F i x) ^ (2 / p)) ^ (p / 2) := by
  obtain ⟨C, hC, hstable⟩ := exists_uniform_glyz_transverse_powerAverage l r A hr
  refine ⟨C, hC, ?_⟩
  intro t ht δ hδ hδ1 g q ι s F hF p hp
  letI := isFiniteMeasure_glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t)
    (show l < A + (l + r) by omega) (pow_pos hδ (r + 1))
  letI := isFiniteMeasure_glyzPolarMeasure hA (glyzMomentFrequencyFrame (l + r) t δ hδ)
  exact glyz_weighted_mixed_l2_absorb s _ _ F _ hF
    (measurable_glyzPowerAverage _ g q) (ENNReal.ofReal C) ENNReal.ofReal_ne_top
    (hstable t ht δ hδ hδ1 g q) hp

end PlanarNikodym
