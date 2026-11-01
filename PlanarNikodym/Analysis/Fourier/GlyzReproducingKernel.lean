import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual Fourier reproducing kernels and the pointwise weighted Hölder
estimate used in GLYZ Lemma 3.3, in arbitrary finite dimension. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform Convolution ENNReal NNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzReproducingKernel (χ : SchwartzMap E ℂ) : SchwartzMap E ℂ := 𝓕⁻ χ

theorem glyz_schwartz_reproducing (f χ : SchwartzMap E ℂ)
    (hχ : ∀ ξ ∈ Function.support (𝓕 (f : E → ℂ)), χ ξ = 1) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] glyzReproducingKernel χ) = (f : E → ℂ) := by
  have he : SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f
      (glyzReproducingKernel χ) = f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap E ℂ)).injective
    rw [FourierTransform.fourierEquiv_apply, FourierTransform.fourierEquiv_apply,
      SchwartzMap.fourier_convolution]
    ext ξ
    change 𝓕 f ξ * 𝓕 (𝓕⁻ χ) ξ = 𝓕 f ξ
    rw [fourier_fourierInv_eq]
    by_cases h : 𝓕 f ξ = 0
    · rw [h, zero_mul]
    · rw [hχ ξ h, mul_one]
  funext x
  rw [← SchwartzMap.convolution_apply]
  exact congrArg (fun g : SchwartzMap E ℂ => g x) he

/-- Pointwise Hölder in the actual kernel measure. The finite measure
and its mass are constructed from the integrable Schwartz kernel. -/
theorem glyz_pointwise_kernel_holder (f K : SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) (x : E) :
    ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] K) x‖ₑ ^ (p : ℝ) ≤
      (∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ‖K y‖ₑ) *
        (∫⁻ y, ‖K y‖ₑ) ^ ((p : ℝ) - 1) := by
  let ν : Measure E := volume.withDensity (fun y => ‖K y‖ₑ)
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    K.integrable.hasFiniteIntegral.ne
  have hm : ν univ = ∫⁻ y, ‖K y‖ₑ := by
    simp [ν, withDensity_apply _ MeasurableSet.univ]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le zero_lt_one hp
  have hbound : ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] K) x‖ₑ ≤
      ∫⁻ y, ‖f (x - y)‖ₑ ∂ν := by
    rw [convolution_eq_swap]
    apply (enorm_integral_le_lintegral_enorm _).trans_eq
    dsimp only [ν]
    rw [lintegral_withDensity_eq_lintegral_mul volume K.continuous.measurable.enorm
      (show Measurable (fun y : E => ‖f (x - y)‖ₑ) from
        (f.continuous.measurable.comp (measurable_id.const_sub x)).enorm)]
    apply lintegral_congr
    intro y
    simp only [ContinuousLinearMap.mul_apply', enorm_mul, Pi.mul_apply, mul_comm]
  have hh := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (μ := ν)
    (f := fun y : E => f (x - y)) zero_lt_one
    (show (1 : ℝ) ≤ p by exact_mod_cast hp)
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  simp only [eLpNorm'_eq_lintegral_enorm, div_one, ENNReal.rpow_one] at hh
  have hh := ENNReal.rpow_le_rpow hh hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hh
  have he1 : (1 / (p : ℝ)) * p = 1 := div_mul_cancel₀ 1 hp0.ne'
  have he2 : (1 - 1 / (p : ℝ)) * p = (p : ℝ) - 1 := by field_simp
  simp only [he1, he2, ENNReal.rpow_one, hm] at hh
  apply (ENNReal.rpow_le_rpow hbound hp0.le).trans
  dsimp only [ν] at hh
  rw [lintegral_withDensity_eq_lintegral_mul volume K.continuous.measurable.enorm
    (show Measurable (fun y : E => ‖f (x - y)‖ₑ ^ (p : ℝ)) from
      (f.continuous.measurable.comp (measurable_id.const_sub x)).enorm.pow_const _)] at hh
  simpa only [ν, Pi.mul_apply, mul_comm] using hh

theorem glyz_pointwise_reproducing_holder (f χ : SchwartzMap E ℂ)
    (hχ : ∀ ξ ∈ Function.support (𝓕 (f : E → ℂ)), χ ξ = 1)
    {p : ℝ≥0} (hp : 1 ≤ p) (x : E) :
    ‖f x‖ₑ ^ (p : ℝ) ≤
      (∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ‖glyzReproducingKernel χ y‖ₑ) *
        (∫⁻ y, ‖glyzReproducingKernel χ y‖ₑ) ^ ((p : ℝ) - 1) := by
  simpa only [glyz_schwartz_reproducing f χ hχ] using
    glyz_pointwise_kernel_holder f (glyzReproducingKernel χ) hp x

end PlanarNikodym
