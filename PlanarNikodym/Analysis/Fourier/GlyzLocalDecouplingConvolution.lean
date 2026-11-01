import PlanarNikodym.Analysis.Fourier.GlyzMixedNormAbsorption
import PlanarNikodym.Analysis.Fourier.GlyzLocalAverage
import PlanarNikodym.Analysis.Fourier.GlyzPositiveConvolution

/-! Passing an explicit local decoupling inequality through an ambient
positive convolution. This is an implication, not a proof of the local
decoupling hypothesis. All changes of integration order are proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

theorem glyz_convolve_local_decoupling {ι : Type*} (s : Finset ι)
    (μ ν : Measure H) (σ : Measure E) [SFinite μ] [SFinite ν] [SFinite σ]
    (S : H →L[ℝ] E) (F : E → ℝ≥0∞) (f : ι → E → ℝ≥0∞)
    (hF : Measurable F) (hf : ∀ i ∈ s, Measurable (f i))
    {p : ℝ} (hp : 2 ≤ p) (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (hlocal : ∀ x, glyzSubspaceAverage μ S F x ≤
      D * (∑ i ∈ s, glyzSubspaceAverage ν S (f i) x ^ (2 / p)) ^ (p / 2))
    (x : E) :
    glyzSubspaceAverage μ S (glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ E) F) x ≤
      D * (∑ i ∈ s, glyzSubspaceAverage ν S
        (glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ E) (f i)) x ^ (2 / p)) ^ (p / 2) := by
  rw [glyzSubspaceAverage_commute μ σ S hF]
  calc
    _ ≤ ∫⁻ y, D * (∑ i ∈ s, glyzSubspaceAverage ν S (f i) (x - y) ^ (2 / p)) ^ (p / 2) ∂σ :=
      lintegral_mono fun y => hlocal (x - y)
    _ = D * ∫⁻ y, (∑ i ∈ s, glyzSubspaceAverage ν S (f i) (x - y) ^ (2 / p)) ^ (p / 2) ∂σ :=
      lintegral_const_mul' _ _ hD
    _ ≤ D * (∑ i ∈ s, (∫⁻ y, glyzSubspaceAverage ν S (f i) (x - y) ∂σ) ^ (2 / p)) ^ (p / 2) := by
      apply mul_le_mul' le_rfl
      exact glyz_lintegral_mixed_l2 σ s _
        (fun i hi => ((measurable_glyzSubspaceAverage ν S (hf i hi)).comp
          (continuous_const.sub continuous_id).measurable).aemeasurable) hp
    _ = _ := by
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      exact (glyzSubspaceAverage_commute ν σ S (hf i hi) x).symm

/-- Uniform replacement of each member of an integrated powered ℓ² sum.
This lemma also covers empty families and infinite extended integrals. -/
theorem glyz_weighted_l2_replace {ι : Type*} (s : Finset ι) (G : E → ℝ≥0∞)
    (F f : ι → E → ℝ≥0∞) {p : ℝ} (hp : 0 < p)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (h : ∀ i ∈ s, ∀ x, F i x ≤ C * f i x) :
    (∑ i ∈ s, (∫⁻ x, G x * F i x) ^ (2 / p)) ^ (p / 2) ≤
      C * (∑ i ∈ s, (∫⁻ x, G x * f i x) ^ (2 / p)) ^ (p / 2) := by
  have hi (i : ι) (hi : i ∈ s) : (∫⁻ x, G x * F i x) ≤ C * ∫⁻ x, G x * f i x := by
    calc
      _ ≤ ∫⁻ x, C * (G x * f i x) := lintegral_mono fun x =>
        (mul_le_mul' le_rfl (h i hi x)).trans_eq (by ring)
      _ = _ := lintegral_const_mul' _ _ hC
  calc
    _ ≤ (∑ i ∈ s, (C * ∫⁻ x, G x * f i x) ^ (2 / p)) ^ (p / 2) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact Finset.sum_le_sum fun i hi' => ENNReal.rpow_le_rpow (hi i hi') (by positivity)
    _ = _ := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 2 / p)]
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ p / 2),
        ← ENNReal.rpow_mul, show 2 / p * (p / 2) = 1 by field_simp, ENNReal.rpow_one]

/-- Complete integral assembly from an explicit local inequality. The
local decoupling hypothesis is retained; all averaging, mixed norms,
weight absorption, and replacement are derived here. -/
theorem glyz_integrated_local_decoupling {ι : Type*} (s : Finset ι)
    (μ ν : Measure H) (σ : Measure E) [IsProbabilityMeasure μ]
    [SFinite ν] [Measure.IsNegInvariant ν] [SFinite σ]
    (S : H →L[ℝ] E) (F G : E → ℝ≥0∞) (f f' : ι → E → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (hf : ∀ i ∈ s, Measurable (f i))
    {p : ℝ} (hp : 2 ≤ p) (D B C K : ℝ≥0∞)
    (hD : D ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hK : K ≠ ⊤)
    (hlocal : ∀ x, glyzSubspaceAverage μ S F x ≤
      D * (∑ i ∈ s, glyzSubspaceAverage ν S (f i) x ^ (2 / p)) ^ (p / 2))
    (hshift : ∀ x, ∀ᵐ z ∂μ, G (x - S z) ≤ B * G x)
    (hstable : ∀ x, glyzSubspaceAverage ν S G x ≤ C * G x)
    (hreplace : ∀ i ∈ s, ∀ x,
      glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ E) (f i) x ≤ K * f' i x) :
    (∫⁻ x, glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ E) F x * G x) ≤
      (B * D * C * K) * (∑ i ∈ s, (∫⁻ x, G x * f' i x) ^ (2 / p)) ^ (p / 2) := by
  let U := fun i => glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ E) (f i)
  have hU (i : ι) (hi : i ∈ s) : Measurable (U i) :=
    measurable_glyzSubspaceAverage σ _ (hf i hi)
  have hfirst := glyz_localize_bilinear μ S
    (measurable_glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ E) hF) hG B hB hshift
  have hmiddle := glyz_weighted_mixed_l2_absorb s ν S U G hU hG C hC hstable hp
  have hlast := glyz_weighted_l2_replace s G U f' (by linarith : 0 < p) K hK hreplace
  calc
    _ ≤ B * ∫⁻ x, glyzSubspaceAverage μ S
        (glyzSubspaceAverage σ (ContinuousLinearMap.id ℝ E) F) x * G x := hfirst
    _ ≤ B * ∫⁻ x, D * (G x * (∑ i ∈ s, glyzSubspaceAverage ν S (U i) x ^ (2 / p)) ^ (p / 2)) := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro x
      exact (mul_le_mul' (glyz_convolve_local_decoupling s μ ν σ S F f hF hf hp D hD hlocal x)
        le_rfl).trans_eq (by ring)
    _ = B * (D * ∫⁻ x, G x * (∑ i ∈ s, glyzSubspaceAverage ν S (U i) x ^ (2 / p)) ^ (p / 2)) := by
      rw [lintegral_const_mul' _ _ hD]
    _ ≤ B * (D * (C * (∑ i ∈ s, (∫⁻ x, G x * U i x) ^ (2 / p)) ^ (p / 2))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hmiddle)
    _ ≤ B * (D * (C * (K * (∑ i ∈ s, (∫⁻ x, G x * f' i x) ^ (2 / p)) ^ (p / 2)))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hlast))
    _ = _ := by ring

end PlanarNikodym
