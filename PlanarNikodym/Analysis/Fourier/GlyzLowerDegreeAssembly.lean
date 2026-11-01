import PlanarNikodym.Analysis.Fourier.GlyzLocalDecouplingConvolution
import PlanarNikodym.Analysis.Fourier.GlyzPowerAverageShift
import PlanarNikodym.Analysis.Fourier.GlyzNestedPowerAverage

/-! The analytic assembly of GLYZ Lemma 3.8 from its local slice
inequality. The local inequality is an explicit remaining hypothesis;
this theorem does not assert the lower-dimensional decoupling theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform
open scoped ENNReal NNReal FourierTransform
namespace PlanarNikodym

/-- Actual parent/child moment boxes, polar weights, transverse ball,
transverse decaying weight, and Schwartz functions. Only the local slice
decoupling estimate is assumed. The uniform assembly constant precedes
all intervals, scales, functions, the number of pieces and local loss D. -/
theorem exists_uniform_glyz_lower_degree_assembly (l r A : ℕ)
    (hr : 0 < r) (hA : l + r < A) (hQ : (l + r) * (l + r + 1) / 2 ≤ A)
    (p : ℝ≥0) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ (g : SchwartzMap (GlyzSpace (l + r)) ℂ) (q c κ : ℝ) (hκ : 0 < κ),
      ∀ (ι : Type) (s : Finset ι) (d η : ι → ℝ) (hη : ∀ i, 0 < η i),
      (∀ i ∈ s, |d i - c| ≤ κ ∧ η i ≤ κ) →
      ∀ f : ι → SchwartzMap (GlyzSpace (l + r)) ℂ,
      (∀ i ∈ s, Function.support (𝓕 (f i : GlyzSpace (l + r) → ℂ)) ⊆
        glyzMomentFrequencyBox (l + r) (d i) (η i) (hη i)) →
      ∀ D : ℝ, 0 ≤ D →
      let μ := glyzBallMeasure ((glyzEuclideanTangentSpace (l + r) r t)ᗮ) ((δ ^ (r + 1))⁻¹)
      let ν := glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t) (A + (l + r)) (δ ^ (r + 1))
      let S := (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL
      let σ := glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) c κ hκ)
      let σ' := fun i => glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) (d i) (η i) (hη i))
      let G := glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q
      (∀ x, glyzSubspaceAverage μ S (fun y => ‖(∑ i ∈ s, f i) y‖ₑ ^ (p : ℝ)) x ≤
        ENNReal.ofReal D * (∑ i ∈ s, glyzSubspaceAverage ν S
          (fun y => ‖f i y‖ₑ ^ (p : ℝ)) x ^ (2 / (p : ℝ))) ^ ((p : ℝ) / 2)) →
      (∫⁻ x, glyzPowerAverage σ (∑ i ∈ s, f i : SchwartzMap (GlyzSpace (l + r)) ℂ) (p : ℝ) x * G x) ≤
        ENNReal.ofReal (C * D) *
          (∑ i ∈ s, (∫⁻ x, glyzPowerAverage (σ' i) (f i) (p : ℝ) x * G x) ^
            (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  obtain ⟨B, hB, hshift⟩ := exists_uniform_glyz_transverse_powerAverage_shift l r A
  obtain ⟨C, hC, hstable⟩ := exists_uniform_glyz_transverse_powerAverage l r A hr
  obtain ⟨K, hK, hreplace⟩ := exists_uniform_glyz_parent_powerAverage_le_child (l + r) A hA hQ
    (show 1 ≤ p by linarith)
  refine ⟨B * C * K, mul_pos (mul_pos hB hC) hK, ?_⟩
  intro t ht δ hδ hδ1 g q c κ hκ ι s d η hη hnested f hs D _hD
  dsimp only
  let μ := glyzBallMeasure ((glyzEuclideanTangentSpace (l + r) r t)ᗮ) ((δ ^ (r + 1))⁻¹)
  let ν := glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t) (A + (l + r)) (δ ^ (r + 1))
  let S := (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL
  let σ := glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) c κ hκ)
  let σ' := fun i => glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) (d i) (η i) (hη i))
  let G := glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q
  intro hlocal
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_glyzBallMeasure (inv_pos.mpr (pow_pos hδ (r + 1)))
  letI : IsFiniteMeasure ν := isFiniteMeasure_glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t)
    (show l < A + (l + r) by omega) (pow_pos hδ (r + 1))
  letI : IsFiniteMeasure σ := isFiniteMeasure_glyzPolarMeasure hA _
  letI := isFiniteMeasure_glyzPolarMeasure hA (glyzMomentFrequencyFrame (l + r) t δ hδ)
  have hF : Measurable (fun y => ‖(∑ i ∈ s, f i) y‖ₑ ^ (p : ℝ)) :=
    (∑ i ∈ s, f i).continuous.measurable.enorm.pow_const _
  have hG : Measurable G := measurable_glyzPowerAverage _ g q
  have hf (i : ι) (_ : i ∈ s) : Measurable (fun y => ‖f i y‖ₑ ^ (p : ℝ)) :=
    (f i).continuous.measurable.enorm.pow_const _
  have hsh (x : GlyzSpace (l + r)) : ∀ᵐ z ∂μ, G (x - S z) ≤ ENNReal.ofReal B * G x :=
    (ae_glyzBallMeasure_norm_le ((δ ^ (r + 1))⁻¹)).mono fun z hz =>
      hshift t ht δ hδ hδ1 g q z hz x
  have hst (x : GlyzSpace (l + r)) : glyzSubspaceAverage ν S G x ≤ ENNReal.ofReal C * G x :=
    hstable t ht δ hδ hδ1 g q x
  have hre (i : ι) (hi : i ∈ s) (x : GlyzSpace (l + r)) :
      glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ (GlyzSpace (l + r)))
        (fun y => ‖f i y‖ₑ ^ (p : ℝ)) x ≤ ENNReal.ofReal K * glyzPowerAverage (σ' i) (f i) (p : ℝ) x :=
    hreplace c (d i) κ (η i) hκ (hη i) (hnested i hi).1 (hnested i hi).2 (f i) (hs i hi) x
  have h := glyz_integrated_local_decoupling s μ ν σ S _ G _
    (fun i => glyzPowerAverage (σ' i) (f i) (p : ℝ)) hF hG hf
    (show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp)
    (ENNReal.ofReal D) (ENNReal.ofReal B) (ENNReal.ofReal C) (ENNReal.ofReal K)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    hlocal hsh hst hre
  have he : ENNReal.ofReal B * ENNReal.ofReal D * ENNReal.ofReal C * ENNReal.ofReal K =
      ENNReal.ofReal (B * C * K * D) := by
    rw [ENNReal.ofReal_mul (mul_pos (mul_pos hB hC) hK).le,
      ENNReal.ofReal_mul (mul_pos hB hC).le, ENNReal.ofReal_mul hB.le]
    ring
  rw [he] at h
  change (∫⁻ x, glyzPowerAverage σ (∑ i ∈ s, f i : SchwartzMap (GlyzSpace (l + r)) ℂ)
    (p : ℝ) x * G x) ≤ ENNReal.ofReal (B * C * K * D) *
      (∑ i ∈ s, (∫⁻ x, glyzPowerAverage (σ' i) (f i) (p : ℝ) x * G x) ^
        (2 / (p : ℝ))) ^ ((p : ℝ) / 2)
  change (∫⁻ x, glyzPowerAverage σ (∑ i ∈ s, f i : SchwartzMap (GlyzSpace (l + r)) ℂ)
    (p : ℝ) x * G x) ≤ ENNReal.ofReal (B * C * K * D) *
      (∑ i ∈ s, (∫⁻ x, G x * glyzPowerAverage (σ' i) (f i) (p : ℝ) x) ^
        (2 / (p : ℝ))) ^ ((p : ℝ) / 2) at h
  simpa only [mul_comm] using h

end PlanarNikodym
