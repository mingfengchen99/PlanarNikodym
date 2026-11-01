import PlanarNikodym.Analysis.Fourier.CompactKernelIntegration
import PlanarNikodym.Analysis.Fourier.GlyzFourierAffine

/-! Absolute Fubini for a compact smooth kernel against an L¹ input.
The resulting Fourier density is the integral of the actual fiber
Fourier transforms. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

variable {E Y : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

theorem integrable_compactKernel_mul_prod (μ : Measure Y) [SFinite μ]
    {g : Y → ℂ} (hg : Integrable g μ)
    {H : E × Y → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    Integrable (fun q : E × Y => H q * g q.2) (volume.prod μ) := by
  let J := Prod.fst '' tsupport H
  have hJ : IsCompact J := hc.isCompact.image continuous_fst
  let S : SchwartzMap (E × Y) ℂ := hc.toSchwartzMap hH
  let C := SchwartzMap.seminorm ℝ 0 0 S
  have hI : Integrable (J.indicator (fun _ : E => C)) volume :=
    (integrableOn_const hJ.measure_ne_top).integrable_indicator hJ.measurableSet
  apply (hI.mul_prod hg.norm).mono'
    (hH.continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
  filter_upwards [] with q
  change ‖H q * g q.2‖ ≤ J.indicator (fun _ : E => C) q.1 * ‖g q.2‖
  by_cases hq : q.1 ∈ J
  · rw [indicator_of_mem hq, norm_mul]
    exact mul_le_mul_of_nonneg_right (S.norm_le_seminorm ℝ q) (norm_nonneg _)
  · have hz : H q = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hq ⟨q, h, rfl⟩
    simp only [hz, zero_mul, norm_zero, indicator_of_notMem hq]
    simp

theorem fourier_compactKernelIntegralSchwartz (μ : Measure Y) [SFinite μ]
    (g : Y → ℂ) (hg : Integrable g μ)
    (H : E × Y → ℂ) (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    (ξ : E) :
    𝓕 (compactKernelIntegralSchwartz μ g hg H hH hc) ξ =
      ∫ y, g y * 𝓕 (fun x => H (x, y)) ξ ∂μ := by
  let e : E → ℂ := fun x => (Real.fourierChar (-inner ℝ x ξ) : ℂ)
  have he : Continuous e :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hnorm (x : E) : ‖e x‖ = 1 := Circle.norm_coe _
  have hi : Integrable (fun q : E × Y => e q.1 * (H q * g q.2)) (volume.prod μ) :=
    (integrable_compactKernel_mul_prod μ hg hH hc).bdd_mul (c := 1)
      (he.comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun q => (hnorm q.1).le)
  calc
    _ = ∫ x, e x * ∫ y, g y * H (x, y) ∂μ := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq]
      rfl
    _ = ∫ x, ∫ y, e x * (H (x, y) * g y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ∫ y, (∫ x, e x * (H (x, y) * g y)) ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Real.fourier_eq, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      change e x * (H (x, y) * g y) = g y * (e x * H (x, y))
      ring

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- Partial Fourier transformation is jointly continuous in the
frequency and the remaining kernel parameter. -/
theorem continuous_compactKernel_partialFourier
    {H : E × Y → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    Continuous (fun q : E × Y => 𝓕 (fun x => H (x, q.2)) q.1) := by
  let J := Prod.fst '' tsupport H
  have hJ : IsCompact J := hc.isCompact.image continuous_fst
  let S : SchwartzMap (E × Y) ℂ := hc.toSchwartzMap hH
  let C := SchwartzMap.seminorm ℝ 0 0 S
  have hI : Integrable (J.indicator (fun _ : E => C)) volume :=
    (integrableOn_const hJ.measure_ne_top).integrable_indicator hJ.measurableSet
  simp only [Real.fourier_eq]
  apply continuous_of_dominated (bound := J.indicator (fun _ : E => C))
  · intro q
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (hH.continuous.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · intro q
    filter_upwards [] with x
    rw [Circle.norm_smul]
    by_cases hx : x ∈ J
    · rw [indicator_of_mem hx]
      exact S.norm_le_seminorm ℝ (x, q.2)
    · have hz : H (x, q.2) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, q.2), h, rfl⟩
      simp [hz, hx]
  · exact hI
  · filter_upwards [] with x
    exact (Real.continuous_fourierChar.comp (by fun_prop)).smul
      (hH.continuous.comp (continuous_const.prodMk continuous_snd))

theorem fourier_character_modulation (f : E → ℂ) (ν ξ : E) :
    𝓕 (fun x => (Real.fourierChar (inner ℝ x ν) : ℂ) * f x) ξ =
      𝓕 f (ξ - ν) := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [inner_sub_right, neg_sub, sub_eq_neg_add, Real.fourierChar.map_add_eq_mul,
    Circle.coe_mul]
  ring
end PlanarNikodym
