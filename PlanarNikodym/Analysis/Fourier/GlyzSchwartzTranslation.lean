import PlanarNikodym.Analysis.Fourier.GlyzBandlimitedLocalization
import Mathlib.MeasureTheory.Group.LIntegral

/-! Actual spatial translations of Schwartz pieces preserve Fourier
support. Haar translation also transports the local ball and its
decaying weight, with no change of constant. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators RealInnerProductSpace
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Translation to the coordinates centered at `a`: its value is
`f (x + a)`. -/
def glyzSchwartzTranslate (a : E) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  f.compSubConstCLM ℂ (-a)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem glyzSchwartzTranslate_apply (a : E) (f : SchwartzMap E ℂ) (x : E) :
    glyzSchwartzTranslate a f x = f (x + a) := by
  simp only [glyzSchwartzTranslate, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyzSchwartzTranslate_sum {ι : Type*} (a : E) (I : Finset ι)
    (f : ι → SchwartzMap E ℂ) :
    glyzSchwartzTranslate a (∑ i ∈ I, f i) = ∑ i ∈ I, glyzSchwartzTranslate a (f i) := by
  ext x
  simp only [glyzSchwartzTranslate_apply, sum_apply]

theorem fourier_glyzSchwartzTranslate (a : E) (f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (glyzSchwartzTranslate a f : E → ℂ) ξ =
      Real.fourierChar (inner ℝ a ξ) • 𝓕 (f : E → ℂ) ξ := by
  have he : (glyzSchwartzTranslate a f : E → ℂ) =
      (f : E → ℂ) ∘ (fun x => x + a) := by
    ext x
    exact glyzSchwartzTranslate_apply a f x
  rw [he]
  exact congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ E) (f : E → ℂ) a) ξ

theorem support_fourier_glyzSchwartzTranslate (a : E) (f : SchwartzMap E ℂ) :
    Function.support (𝓕 (glyzSchwartzTranslate a f : E → ℂ)) =
      Function.support (𝓕 (f : E → ℂ)) := by
  ext ξ
  simp only [Function.mem_support, fourier_glyzSchwartzTranslate,
    Circle.smul_def, smul_eq_mul, ne_eq, mul_eq_zero, Circle.coe_ne_zero, false_or]

/-- Translation transports a local integral on the origin ball to the
ball with the same radius about `a`. -/
theorem glyz_lintegral_closedBall_translate (a : E) (R : ℝ)
    (F : E → ℝ≥0∞) :
    (∫⁻ x in closedBall (0 : E) R, F (x + a)) =
      ∫⁻ x in closedBall a R, F x := by
  have hpre : (fun x : E => x + a) ⁻¹' closedBall a R = closedBall (0 : E) R := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero]
  have h := (measurePreserving_add_right (volume : Measure E) a).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding F (closedBall a R)
  simpa only [hpre] using h

/-- The weight moves by exactly the same spatial translation as the
local ball. This identity needs no integrability hypothesis. -/
theorem glyz_lintegral_translate_weight (a : E) (F w : E → ℝ≥0∞) :
    (∫⁻ x, F (x + a) * w x) = ∫⁻ x, F x * w (x - a) := by
  have h := lintegral_add_right_eq_self (fun x => F x * w (x - a)) a
    (μ := (volume : Measure E))
  simpa only [add_sub_cancel_right] using h

theorem glyz_lintegral_schwartz_translate_weight (a : E) (f : SchwartzMap E ℂ)
    (p : ℝ) (w : E → ℝ≥0∞) :
    (∫⁻ x, ‖glyzSchwartzTranslate a f x‖ₑ ^ p * w x) =
      ∫⁻ x, ‖f x‖ₑ ^ p * w (x - a) := by
  simp only [glyzSchwartzTranslate_apply]
  exact glyz_lintegral_translate_weight a (fun x => ‖f x‖ₑ ^ p) w

/-- Uniform probability measure on the physical ball about `a`. -/
def glyzCenteredBallMeasure (a : E) (R : ℝ) : Measure E :=
  (volume (closedBall a R))⁻¹ • volume.restrict (closedBall a R)

theorem isProbabilityMeasure_glyzCenteredBallMeasure (a : E) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (glyzCenteredBallMeasure a R) := by
  constructor
  simp only [glyzCenteredBallMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_closedBall_pos volume a hR).ne'
    measure_closedBall_lt_top.ne

/-- Normalizing the local ball and every weighted piece cancels exactly
in the homogeneous square-sum expression. -/
theorem glyz_normalize_centered_local_decoupling {ι : Type*} (s : Finset ι)
    (f : ι → SchwartzMap E ℂ) (a : E) {R p : ℝ} (hR : 0 < R) (hp : 0 < p)
    (w : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hlocal : (∫⁻ x in closedBall a R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤ D *
      (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p * w x) ^ (2 / p)) ^ (p / 2)) :
    (∫⁻ x, ‖(∑ i ∈ s, f i) x‖ₑ ^ p ∂glyzCenteredBallMeasure a R) ≤ D *
      (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p *
        ((volume (closedBall a R))⁻¹ * w x)) ^ (2 / p)) ^ (p / 2) := by
  let c : ℝ≥0∞ := (volume (closedBall a R))⁻¹
  have hc : c ≠ ⊤ := ENNReal.inv_ne_top.mpr (measure_closedBall_pos volume a hR).ne'
  have hi (i : ι) : (∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)) =
      c * ∫⁻ x, ‖f i x‖ₑ ^ p * w x := by
    simp_rw [mul_left_comm (‖f i _‖ₑ ^ p) c]
    exact lintegral_const_mul' _ _ hc
  change (∫⁻ x, ‖(∑ i ∈ s, f i) x‖ₑ ^ p ∂glyzCenteredBallMeasure a R) ≤ D *
    (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)) ^ (2 / p)) ^ (p / 2)
  simp_rw [hi]
  rw [glyz_power_square_sum_mul s _ c hp, glyzCenteredBallMeasure,
    lintegral_smul_measure, smul_eq_mul]
  change c * _ ≤ D * (c * _)
  calc
    _ ≤ c * (D * (∑ i ∈ s, (∫⁻ x, ‖f i x‖ₑ ^ p * w x) ^ (2 / p)) ^ (p / 2)) :=
      mul_le_mul_right hlocal c
    _ = _ := by ring

end PlanarNikodym
