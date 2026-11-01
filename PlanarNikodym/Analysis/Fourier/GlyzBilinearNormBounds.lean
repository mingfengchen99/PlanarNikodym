import PlanarNikodym.Analysis.Fourier.GlyzBilinearFiniteness
import PlanarNikodym.Analysis.Fourier.GlyzAffineLpTransfer

/-! A priori bounds for the actual asymmetric bilinear integrals in
terms of squared Lp norms. Both zero-power endpoints are included. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

def glyzPolarMass (m A : ℕ) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * ∫ x : Base m, glyzDecayWeight A x

theorem glyzPolarMass_nonneg (m A : ℕ) : 0 ≤ glyzPolarMass m A := by
  exact mul_nonneg (by positivity) (integral_nonneg fun x => (glyzDecayWeight_pos A x).le)

theorem glyzPolarMass_pos {m A : ℕ} (hA : m < A) : 0 < glyzPolarMass m A := by
  apply mul_pos (by positivity)
  exact integral_pos_of_integrable_nonneg_nonzero (continuous_glyzDecayWeight A)
    (integrable_glyzDecayWeight hA) (fun x => (glyzDecayWeight_pos A x).le)
    (glyzDecayWeight_pos A (0 : Base m)).ne'

theorem glyzPolarMeasure_univ {m A : ℕ} (hA : m < A)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :
    glyzPolarMeasure A L univ = ENNReal.ofReal (glyzPolarMass m A) := by
  rw [glyzPolarMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal (integrable_glyzPolarWeight hA L)
      (Filter.Eventually.of_forall fun x => (glyzPolarWeight_pos A L x).le),
    integral_glyzPolarWeight]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_lintegral_le_sq_lpNorm_bound (f : SchwartzMap E ℂ) {p : ℝ≥0}
    (hp : 0 < p) {X : ℝ}
    (hf : lpNorm (f : E → ℂ) p volume ^ (2 : ℕ) ≤ X) :
    (∫⁻ x, ‖f x‖ₑ ^ (p : ℝ)) ≤ ENNReal.ofReal X ^ ((p : ℝ) / 2) := by
  have hsq : eLpNorm (f : E → ℂ) p volume ^ (2 : ℕ) ≤ ENNReal.ofReal X := by
    rw [← ofReal_lpNorm (f.memLp p volume), ← ENNReal.ofReal_pow lpNorm_nonneg]
    exact ENNReal.ofReal_le_ofReal hf
  rw [← eLpNorm_nnreal_pow_eq_lintegral hp.ne']
  calc
    _ = (eLpNorm (f : E → ℂ) p volume ^ (2 : ℕ)) ^ ((p : ℝ) / 2) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      ring
    _ ≤ _ := ENNReal.rpow_le_rpow hsq (by positivity)

/-- The estimate holds for every pair of finite averaging measures,
including the zero exponents. The only bounds on the functions are
their explicit squared Lp norms. -/
theorem glyzWeightedBilinear_le_sq_lpNorm_bounds
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : SchwartzMap E ℂ) {p : ℝ≥0} (hp : 0 < p)
    {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) {X Y : ℝ}
    (hf : lpNorm (f : E → ℂ) p volume ^ (2 : ℕ) ≤ X)
    (hg : lpNorm (g : E → ℂ) p volume ^ (2 : ℕ) ≤ Y) :
    glyzWeightedBilinear μ ν f g a ((p : ℝ) - a) ≤
      (μ univ * ν univ) *
        (ENNReal.ofReal X ^ (a / 2) * ENNReal.ofReal Y ^ (((p : ℝ) - a) / 2)) := by
  have hf' := glyz_lintegral_le_sq_lpNorm_bound f hp hf
  have hg' := glyz_lintegral_le_sq_lpNorm_bound g hp hg
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0, sub_zero, glyzWeightedBilinear_zero_left]
    simpa using mul_le_mul_right hg' (μ univ * ν univ)
  rcases eq_or_lt_of_le hap with hap0 | hap0
  · rw [hap0, sub_self, glyzWeightedBilinear_symm, glyzWeightedBilinear_zero_left]
    simpa [mul_comm] using mul_le_mul_right hf' (ν univ * μ univ)
  have hp' : (0 : ℝ) < p := hp
  have hθ : 0 < a / (p : ℝ) := div_pos ha0 hp'
  have hθ1 : a / (p : ℝ) < 1 := (div_lt_one hp').mpr hap0
  have h₁ : a / (p : ℝ) * p = a := div_mul_cancel₀ a hp'.ne'
  have h₂ : (1 - a / (p : ℝ)) * p = (p : ℝ) - a := by field_simp
  have h := glyzWeightedBilinear_holder_bound μ ν f g hp'.le hθ hθ1
  rw [h₁, h₂] at h
  apply h.trans
  have hF := ENNReal.rpow_le_rpow hf' hθ.le
  have hG := ENNReal.rpow_le_rpow hg' (sub_pos.mpr hθ1).le
  rw [← ENNReal.rpow_mul] at hF hG
  have h₃ : (p : ℝ) / 2 * (a / p) = a / 2 := by field_simp
  have h₄ : (p : ℝ) / 2 * (1 - a / p) = ((p : ℝ) - a) / 2 := by field_simp
  rw [h₃] at hF
  rw [h₄] at hG
  exact mul_le_mul_right (mul_le_mul' hF hG) _

/-- The constant for the actual polar weights is independent of both
frames, hence of all interval centers and scales. -/
theorem glyz_polar_bilinear_le_sq_lpNorm_bounds {m A : ℕ} (hA : m < A)
    (L₁ L₂ : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (f g : SchwartzMap (GlyzSpace m) ℂ) {p : ℝ≥0} (hp : 0 < p)
    {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) {X Y : ℝ}
    (hf : lpNorm (f : GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤ X)
    (hg : lpNorm (g : GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤ Y) :
    glyzWeightedBilinear (glyzPolarMeasure A L₁) (glyzPolarMeasure A L₂)
      f g a ((p : ℝ) - a) ≤
      ENNReal.ofReal (glyzPolarMass m A ^ (2 : ℕ)) *
        (ENNReal.ofReal X ^ (a / 2) * ENNReal.ofReal Y ^ (((p : ℝ) - a) / 2)) := by
  letI := isFiniteMeasure_glyzPolarMeasure hA L₁
  letI := isFiniteMeasure_glyzPolarMeasure hA L₂
  have h := glyzWeightedBilinear_le_sq_lpNorm_bounds
    (glyzPolarMeasure A L₁) (glyzPolarMeasure A L₂) f g hp ha hap hf hg
  rw [glyzPolarMeasure_univ hA, glyzPolarMeasure_univ hA, ← pow_two,
    ← ENNReal.ofReal_pow (glyzPolarMass_nonneg m A)] at h
  exact h

theorem glyz_polar_bilinear_toReal_le_sq_lpNorm_bounds {m A : ℕ} (hA : m < A)
    (L₁ L₂ : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (f g : SchwartzMap (GlyzSpace m) ℂ) {p : ℝ≥0} (hp : 0 < p)
    {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) {X Y : ℝ}
    (hf : lpNorm (f : GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤ X)
    (hg : lpNorm (g : GlyzSpace m → ℂ) p volume ^ (2 : ℕ) ≤ Y) :
    (glyzWeightedBilinear (glyzPolarMeasure A L₁) (glyzPolarMeasure A L₂)
      f g a ((p : ℝ) - a)).toReal ≤
      glyzPolarMass m A ^ (2 : ℕ) * (X ^ (a / 2) * Y ^ (((p : ℝ) - a) / 2)) := by
  have h := glyz_polar_bilinear_le_sq_lpNorm_bounds hA L₁ L₂ f g hp ha hap hf hg
  have hX : 0 ≤ X := (sq_nonneg _).trans hf
  have hY : 0 ≤ Y := (sq_nonneg _).trans hg
  have hfinite : ENNReal.ofReal (glyzPolarMass m A ^ (2 : ℕ)) *
      (ENNReal.ofReal X ^ (a / 2) * ENNReal.ofReal Y ^ (((p : ℝ) - a) / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top))
  have ht := ENNReal.toReal_mono hfinite h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hX,
    ENNReal.toReal_ofReal hY] using ht

end PlanarNikodym
