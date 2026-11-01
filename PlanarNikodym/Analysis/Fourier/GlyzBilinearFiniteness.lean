import PlanarNikodym.Analysis.Fourier.GlyzPowerAverageMass
import PlanarNikodym.Analysis.Fourier.GlyzPolarBilinearMeasure

/-! Finiteness of the actual convolution-power bilinear quantities,
including both zero-power endpoints. No decoupling gain is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_schwartz_lintegral_rpow_lt_top (f : SchwartzMap E ℂ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖f x‖ₑ ^ p) < ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ENNReal.ofReal p) (by positivity) ENNReal.ofReal_ne_top
    (f.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top
  simpa only [ENNReal.toReal_ofReal hp.le] using h

theorem glyzWeightedBilinear_symm (μ ν : Measure E) (f g : E → ℂ) (a b : ℝ) :
    glyzWeightedBilinear μ ν f g a b = glyzWeightedBilinear ν μ g f b a := by
  unfold glyzWeightedBilinear
  apply lintegral_congr
  intro x
  exact mul_comm _ _

theorem glyzWeightedBilinear_lt_top (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : SchwartzMap E ℂ) {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hap : a ≤ p) :
    glyzWeightedBilinear μ ν f g a (p - a) < ⊤ := by
  have hf := (glyz_schwartz_lintegral_rpow_lt_top f hp).ne
  have hg := (glyz_schwartz_lintegral_rpow_lt_top g hp).ne
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0, sub_zero, glyzWeightedBilinear_zero_left]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _))
      (lt_top_iff_ne_top.mpr hg)
  rcases eq_or_lt_of_le hap with hap0 | hap0
  · rw [hap0, sub_self, glyzWeightedBilinear_symm, glyzWeightedBilinear_zero_left]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _))
      (lt_top_iff_ne_top.mpr hf)
  let θ := a / p
  have hθ : 0 < θ := div_pos ha0 hp
  have hθ1 : θ < 1 := (div_lt_one hp).mpr hap0
  have hθp : θ * p = a := div_mul_cancel₀ a hp.ne'
  have hθp' : (1 - θ) * p = p - a := by dsimp [θ]; field_simp
  have h := glyzWeightedBilinear_holder_bound μ ν f g hp.le hθ hθ1
  rw [hθp, hθp'] at h
  apply lt_of_le_of_lt h
  apply lt_top_iff_ne_top.mpr
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ.le hf)
      (ENNReal.rpow_ne_top_of_nonneg (sub_pos.mpr hθ1).le hg))

theorem glyz_polar_bilinear_lt_top {m A : ℕ} (hA : m < A)
    (L₁ L₂ : GlyzSpace m ≃L[ℝ] GlyzSpace m) (f g : SchwartzMap (GlyzSpace m) ℂ)
    {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hap : a ≤ p) :
    glyzWeightedBilinear (glyzPolarMeasure A L₁) (glyzPolarMeasure A L₂) f g a (p - a) < ⊤ := by
  letI := isFiniteMeasure_glyzPolarMeasure hA L₁
  letI := isFiniteMeasure_glyzPolarMeasure hA L₂
  exact glyzWeightedBilinear_lt_top _ _ f g hp ha hap

end PlanarNikodym
