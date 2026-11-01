import PlanarNikodym.Analysis.Fourier.GlyzWeightedHolder
import Mathlib.MeasureTheory.Group.LIntegral

/-! Exact mass and a priori Holder bounds for the actual weighted
bilinear integral. These are finite-scale bounds, not decoupling gains. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem glyzPowerAverage_zero (μ : Measure E) (f : E → ℂ) (x : E) :
    glyzPowerAverage μ f 0 x = μ univ := by simp [glyzPowerAverage]

theorem glyz_lintegral_powerAverage (μ : Measure E) [SFinite μ]
    (f : SchwartzMap E ℂ) (p : ℝ) :
    (∫⁻ x, glyzPowerAverage μ f p x) = μ univ * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hf : Measurable (fun z : E × E => ‖f (z.1 - z.2)‖ₑ ^ p) :=
    (f.continuous.comp (continuous_fst.sub continuous_snd)).measurable.enorm.pow_const p
  unfold glyzPowerAverage
  rw [lintegral_lintegral_swap hf.aemeasurable]
  simp_rw [lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ p)]
  rw [lintegral_const, mul_comm]

theorem glyzWeightedBilinear_zero_left (μ ν : Measure E) [SFinite ν]
    (f g : SchwartzMap E ℂ) (p : ℝ) :
    glyzWeightedBilinear μ ν f g 0 p = μ univ * ν univ * ∫⁻ x, ‖g x‖ₑ ^ p := by
  unfold glyzWeightedBilinear
  simp_rw [glyzPowerAverage_zero]
  rw [lintegral_const_mul _ (measurable_glyzPowerAverage ν g p), glyz_lintegral_powerAverage]
  exact (mul_assoc _ _ _).symm

theorem glyzWeightedBilinear_holder_bound (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : SchwartzMap E ℂ) {p θ : ℝ} (hp : 0 ≤ p) (hθ : 0 < θ) (hθ1 : θ < 1) :
    glyzWeightedBilinear μ ν f g (θ * p) ((1 - θ) * p) ≤
      (μ univ * ν univ) * ((∫⁻ x, ‖f x‖ₑ ^ p) ^ θ * (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 - θ)) := by
  let M : ℝ≥0∞ := μ univ ^ (1 - θ) * ν univ ^ θ
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_pos.mpr hθ1).le (measure_ne_top _ _))
    (ENNReal.rpow_ne_top_of_nonneg hθ.le (measure_ne_top _ _))
  have hpoint (x : E) :
      glyzPowerAverage μ f (θ * p) x * glyzPowerAverage ν g ((1 - θ) * p) x ≤
        M * (glyzPowerAverage μ f p x ^ θ * glyzPowerAverage ν g p x ^ (1 - θ)) := by
    have h₁ := glyzPowerAverage_logconvex μ f (a₀ := 0) (a₁ := p) (by norm_num) hp hθ hθ1 x
    have h₂ := glyzPowerAverage_logconvex ν g (a₀ := 0) (a₁ := p) (by norm_num) hp
      (sub_pos.mpr hθ1) (by linarith : 1 - θ < 1) x
    have he : 1 - (1 - θ) = θ := by ring
    simp only [mul_zero, add_zero, glyzPowerAverage_zero, he] at h₁ h₂
    apply (mul_le_mul' h₁ h₂).trans_eq
    dsimp [M]
    ring
  calc
    _ ≤ ∫⁻ x, M * (glyzPowerAverage μ f p x ^ θ * glyzPowerAverage ν g p x ^ (1 - θ)) :=
      lintegral_mono hpoint
    _ = M * ∫⁻ x, glyzPowerAverage μ f p x ^ θ * glyzPowerAverage ν g p x ^ (1 - θ) :=
      lintegral_const_mul' _ _ hM
    _ ≤ M * ((∫⁻ x, glyzPowerAverage μ f p x) ^ θ *
        (∫⁻ x, glyzPowerAverage ν g p x) ^ (1 - θ)) := by
      gcongr
      exact glyz_lintegral_logconvex volume (measurable_glyzPowerAverage μ f p).aemeasurable
        (measurable_glyzPowerAverage ν g p).aemeasurable hθ hθ1
    _ = _ := by
      rw [glyz_lintegral_powerAverage, glyz_lintegral_powerAverage,
        ENNReal.mul_rpow_of_nonneg _ _ hθ.le,
        ENNReal.mul_rpow_of_nonneg _ _ (sub_pos.mpr hθ1).le]
      have hm (a : ℝ≥0∞) : a ^ (1 - θ) * a ^ θ = a := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_pos.mpr hθ1).le hθ.le]
        simp
      dsimp [M]
      calc
        _ = ((μ univ ^ (1 - θ) * μ univ ^ θ) *
            (ν univ ^ (1 - θ) * ν univ ^ θ)) *
              ((∫⁻ x, ‖f x‖ₑ ^ p) ^ θ * (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 - θ)) := by ring
        _ = _ := by rw [hm, hm]

end PlanarNikodym
