import PlanarNikodym.Analysis.Fourier.GlyzPolarWeightMass
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Actual weighted power averages and the two-stage Holder inequality
used for the asymmetric bilinear recursion. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem glyz_lintegral_logconvex {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F G : α → ℝ≥0∞} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫⁻ x, F x ^ θ * G x ^ (1 - θ) ∂μ) ≤
      (∫⁻ x, F x ∂μ) ^ θ * (∫⁻ x, G x ∂μ) ^ (1 - θ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (Real.HolderConjugate.inv_one_sub_inv hθ hθ1)
    (hF.pow_const θ) (hG.pow_const (1 - θ))
  simpa only [Pi.mul_apply, ← ENNReal.rpow_mul, mul_inv_cancel₀ hθ.ne',
    mul_inv_cancel₀ (sub_pos.mpr hθ1).ne', ENNReal.rpow_one, one_div, inv_inv] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzPowerAverage (μ : Measure E) (f : E → ℂ) (a : ℝ) (x : E) : ℝ≥0∞ :=
  ∫⁻ y, ‖f (x - y)‖ₑ ^ a ∂μ

theorem measurable_glyzPowerAverage (μ : Measure E) [SFinite μ]
    (f : SchwartzMap E ℂ) (a : ℝ) : Measurable (glyzPowerAverage μ f a) := by
  apply Measurable.lintegral_prod_right
  exact (f.continuous.comp (continuous_fst.sub continuous_snd)).measurable.enorm.pow_const a

omit [FiniteDimensional ℝ E] in
theorem glyzPowerAverage_logconvex (μ : Measure E) (f : SchwartzMap E ℂ)
    {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hθ : 0 < θ) (hθ1 : θ < 1) (x : E) :
    glyzPowerAverage μ f (θ * a₁ + (1 - θ) * a₀) x ≤
      glyzPowerAverage μ f a₁ x ^ θ * glyzPowerAverage μ f a₀ x ^ (1 - θ) := by
  have hf : Measurable (fun y => ‖f (x - y)‖ₑ) :=
    (f.continuous.comp (continuous_const.sub continuous_id)).measurable.enorm
  have h := glyz_lintegral_logconvex μ (hf.pow_const a₁).aemeasurable
    (hf.pow_const a₀).aemeasurable hθ hθ1
  have he (y : E) : ‖f (x - y)‖ₑ ^ (θ * a₁ + (1 - θ) * a₀) =
      (‖f (x - y)‖ₑ ^ a₁) ^ θ * (‖f (x - y)‖ₑ ^ a₀) ^ (1 - θ) := by
    rw [ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hθ.le ha₁)
      (mul_nonneg (sub_pos.mpr hθ1).le ha₀),
      mul_comm θ a₁, mul_comm (1 - θ) a₀, ENNReal.rpow_mul, ENNReal.rpow_mul]
  simpa only [glyzPowerAverage, he] using h

def glyzWeightedBilinear (μ ν : Measure E) (f g : E → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, glyzPowerAverage μ f a x * glyzPowerAverage ν g b x

theorem glyzWeightedBilinear_logconvex (μ ν : Measure E) [SFinite μ] [SFinite ν]
    (f g : SchwartzMap E ℂ) {a₀ a₁ b₀ b₁ θ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    glyzWeightedBilinear μ ν f g (θ * a₁ + (1 - θ) * a₀) (θ * b₁ + (1 - θ) * b₀) ≤
      glyzWeightedBilinear μ ν f g a₁ b₁ ^ θ *
        glyzWeightedBilinear μ ν f g a₀ b₀ ^ (1 - θ) := by
  apply le_trans (lintegral_mono fun x => mul_le_mul'
    (glyzPowerAverage_logconvex μ f ha₀ ha₁ hθ hθ1 x)
    (glyzPowerAverage_logconvex ν g hb₀ hb₁ hθ hθ1 x))
  have he (x : E) : (glyzPowerAverage μ f a₁ x ^ θ * glyzPowerAverage μ f a₀ x ^ (1 - θ)) *
      (glyzPowerAverage ν g b₁ x ^ θ * glyzPowerAverage ν g b₀ x ^ (1 - θ)) =
      (glyzPowerAverage μ f a₁ x * glyzPowerAverage ν g b₁ x) ^ θ *
        (glyzPowerAverage μ f a₀ x * glyzPowerAverage ν g b₀ x) ^ (1 - θ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le,
      ENNReal.mul_rpow_of_nonneg _ _ (sub_pos.mpr hθ1).le]
    ring
  simp_rw [he]
  exact glyz_lintegral_logconvex volume
    ((measurable_glyzPowerAverage μ f a₁).mul (measurable_glyzPowerAverage ν g b₁)).aemeasurable
    ((measurable_glyzPowerAverage μ f a₀).mul (measurable_glyzPowerAverage ν g b₀)).aemeasurable hθ hθ1

end PlanarNikodym
