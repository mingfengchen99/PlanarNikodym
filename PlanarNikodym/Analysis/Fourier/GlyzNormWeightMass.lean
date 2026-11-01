import PlanarNikodym.Analysis.Fourier.GlyzSchwartzTranslation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! The polynomial localization weight has finite positive mass and
an exact mass scaling in every finite-dimensional Euclidean space. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_glyzNormWeight (A : ℕ) : Continuous (glyzNormWeight (E := E) A) := by
  unfold glyzNormWeight
  exact ((continuous_const.max continuous_norm).pow A).inv₀ (fun x => by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyzNormWeight_le_japanese (A : ℕ) (x : E) :
    glyzNormWeight A x ≤ 2 ^ A * (1 + ‖x‖) ^ (-(A : ℝ)) := by
  have hm : 0 < max (1 : ℝ) ‖x‖ := zero_lt_one.trans_le (le_max_left _ _)
  have hx : 0 < 1 + ‖x‖ := by positivity
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]
  change (max 1 ‖x‖ ^ A)⁻¹ ≤ 2 ^ A * ((1 + ‖x‖) ^ A)⁻¹
  have hb : 1 + ‖x‖ ≤ 2 * max (1 : ℝ) ‖x‖ := by
    linarith [le_max_left (1 : ℝ) ‖x‖, le_max_right (1 : ℝ) ‖x‖]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖) hb A
  rw [mul_pow] at hpow
  have he : (1 : ℝ) / max 1 ‖x‖ ^ A ≤ (2 : ℝ) ^ A / (1 + ‖x‖) ^ A :=
    (div_le_div_iff₀ (pow_pos hm A) (pow_pos hx A)).mpr (by simpa using hpow)
  simpa only [one_div, div_eq_mul_inv, one_mul] using he

theorem integrable_glyzNormWeight {A : ℕ} (hA : Module.finrank ℝ E < A) :
    Integrable (glyzNormWeight (E := E) A) := by
  have hr : (Module.finrank ℝ E : ℝ) < (A : ℝ) := by exact_mod_cast hA
  apply ((integrable_one_add_norm (E := E) (μ := volume) hr).const_mul ((2 : ℝ) ^ A)).mono'
    (continuous_glyzNormWeight A).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x =>
    (abs_of_pos (glyzNormWeight_pos A x)).trans_le (glyzNormWeight_le_japanese A x)

theorem glyz_lintegral_comp_smul (W : E → ℝ≥0∞) {b : ℝ} (hb : b ≠ 0) :
    (∫⁻ x, W (b • x)) = ENNReal.ofReal |(b ^ Module.finrank ℝ E)⁻¹| * ∫⁻ x, W x := by
  let e : E ≃ᵐ E := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hb).unit).toMeasurableEquiv
  have h := lintegral_map_equiv W e (μ := (volume : Measure E))
  change (∫⁻ x, W x ∂Measure.map (fun y : E => b • y) volume) = ∫⁻ x, W (b • x) at h
  rw [Measure.map_addHaar_smul volume hb, lintegral_smul_measure, smul_eq_mul] at h
  exact h.symm

theorem glyz_lintegral_normWeight_smul_sub (A : ℕ) {b : ℝ} (hb : 0 < b) (a : E) :
    (∫⁻ x, ENNReal.ofReal (glyzNormWeight A (b • (x - a)))) =
      ENNReal.ofReal ((b ^ Module.finrank ℝ E)⁻¹) *
        ∫⁻ x : E, ENNReal.ofReal (glyzNormWeight A x) := by
  rw [lintegral_sub_right_eq_self (fun x : E => ENNReal.ofReal (glyzNormWeight A (b • x))) a,
    glyz_lintegral_comp_smul (fun x : E => ENNReal.ofReal (glyzNormWeight A x)) hb.ne',
    abs_of_pos (inv_pos.mpr (pow_pos hb _))]

theorem glyzNormWeight_lintegral_ne_top {A : ℕ} (hA : Module.finrank ℝ E < A) :
    (∫⁻ x : E, ENNReal.ofReal (glyzNormWeight A x)) ≠ ⊤ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_glyzNormWeight hA)
    (Filter.Eventually.of_forall fun x => (glyzNormWeight_pos A x).le)]
  exact ENNReal.ofReal_ne_top

theorem glyzNormWeight_lintegral_pos (A : ℕ) :
    0 < ∫⁻ x : E, ENNReal.ofReal (glyzNormWeight A x) := by
  have he : (∫⁻ x in closedBall (0 : E) 1, ENNReal.ofReal (glyzNormWeight A x)) =
      volume (closedBall (0 : E) 1) := by
    calc
      _ = ∫⁻ _x in closedBall (0 : E) 1, (1 : ℝ≥0∞) := by
        apply setLIntegral_congr_fun measurableSet_closedBall
        intro x hx
        have hx' : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
        simp only [glyzNormWeight, max_eq_left hx', one_pow, inv_one, ENNReal.ofReal_one]
      _ = _ := by simp
  exact (show 0 < ∫⁻ x in closedBall (0 : E) 1, ENNReal.ofReal (glyzNormWeight A x) by
    rw [he]; exact measure_closedBall_pos volume _ zero_lt_one).trans_le
      (setLIntegral_le_lintegral _ _)

end PlanarNikodym
