import PlanarNikodym.Analysis.Maximal.E2FIOPositiveSchur

/-! The quadratic-form Schur bound needed for T*T. Unlike bounding the
norm of T*T twice, this keeps the square-root gain for the original
oscillatory integral operator. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace PlanarNikodym
variable {X : Type*} [MeasurableSpace X]

theorem e2_lintegral_mul_sq_le_sq_mul_sq (μ : Measure X) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ x, f x ^ (2 : ℕ) ∂μ) * ∫⁻ x, g x ^ (2 : ℕ) ∂μ := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hf.aemeasurable hg.aemeasurable
  have hh2 := pow_le_pow_left₀ (show (0 : ℝ≥0∞) ≤ ∫⁻ x, f x * g x ∂μ from zero_le) hh 2
  simpa only [Pi.mul_apply, mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] using hh2

theorem e2_positive_kernel_bilinear_schur (μ : Measure X) [SFinite μ]
    {κ : X → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (hκ : Measurable (Function.uncurry κ)) (hf : Measurable f)
    (A : ℝ≥0∞) (hrow : ∀ x, ∫⁻ y, κ x y ∂μ ≤ A)
    (hcol : ∀ y, ∫⁻ x, κ x y ∂μ ≤ A) :
    (∫⁻ x, ∫⁻ y, κ x y * (f x * f y) ∂μ ∂μ) ≤ A * ∫⁻ x, f x ^ (2 : ℕ) ∂μ := by
  let ν := (μ.prod μ).withDensity (Function.uncurry κ)
  have hfx : Measurable (fun z : X × X => f z.1) := hf.comp measurable_fst
  have hfy : Measurable (fun z : X × X => f z.2) := hf.comp measurable_snd
  have hh := e2_lintegral_mul_sq_le_sq_mul_sq ν hfx hfy
  rw [lintegral_withDensity_eq_lintegral_mul (μ.prod μ) hκ (hfx.mul hfy),
    lintegral_withDensity_eq_lintegral_mul (μ.prod μ) hκ (hfx.pow_const 2),
    lintegral_withDensity_eq_lintegral_mul (μ.prod μ) hκ (hfy.pow_const 2)] at hh
  have h1 : (∫⁻ z : X × X, κ z.1 z.2 * f z.1 ^ (2 : ℕ) ∂μ.prod μ) ≤
      A * ∫⁻ x, f x ^ (2 : ℕ) ∂μ := by
    rw [lintegral_prod (μ := μ) (ν := μ) (fun z : X × X => κ z.1 z.2 * f z.1 ^ (2 : ℕ)) (hκ.mul (hfx.pow_const 2)).aemeasurable]
    calc
      _ = ∫⁻ x, (∫⁻ y, κ x y ∂μ) * f x ^ (2 : ℕ) ∂μ := by
        congr 1
        funext x
        exact lintegral_mul_const (μ := μ) (f := fun y => κ x y) (f x ^ (2 : ℕ))
          (hκ.comp (measurable_const.prodMk measurable_id))
      _ ≤ ∫⁻ x, A * f x ^ (2 : ℕ) ∂μ := lintegral_mono (fun x => mul_le_mul_left (hrow x) _)
      _ = _ := lintegral_const_mul A (hf.pow_const 2)
  have h2 : (∫⁻ z : X × X, κ z.1 z.2 * f z.2 ^ (2 : ℕ) ∂μ.prod μ) ≤
      A * ∫⁻ x, f x ^ (2 : ℕ) ∂μ := by
    rw [lintegral_prod (μ := μ) (ν := μ) (fun z : X × X => κ z.1 z.2 * f z.2 ^ (2 : ℕ)) (hκ.mul (hfy.pow_const 2)).aemeasurable,
      lintegral_lintegral_swap (hκ.mul (hfy.pow_const 2)).aemeasurable]
    calc
      _ = ∫⁻ y, (∫⁻ x, κ x y ∂μ) * f y ^ (2 : ℕ) ∂μ := by
        congr 1
        funext y
        exact lintegral_mul_const (μ := μ) (f := fun x => κ x y) (f y ^ (2 : ℕ))
          (hκ.comp (measurable_id.prodMk measurable_const))
      _ ≤ ∫⁻ x, A * f x ^ (2 : ℕ) ∂μ := lintegral_mono (fun y => mul_le_mul_left (hcol y) _)
      _ = _ := lintegral_const_mul A (hf.pow_const 2)
  have hb := hh.trans (mul_le_mul' h1 h2)
  change (∫⁻ z : X × X, κ z.1 z.2 * (f z.1 * f z.2) ∂μ.prod μ) ^ (2 : ℕ) ≤ _ at hb
  rw [lintegral_prod (μ := μ) (ν := μ) (fun z : X × X => κ z.1 z.2 * (f z.1 * f z.2)) (hκ.mul (hfx.mul hfy)).aemeasurable] at hb
  have he : (A * ∫⁻ x, f x ^ (2 : ℕ) ∂μ) * (A * ∫⁻ x, f x ^ (2 : ℕ) ∂μ) =
      (A * ∫⁻ x, f x ^ (2 : ℕ) ∂μ) ^ (2 : ℕ) := (pow_two _).symm
  rw [he, ← ENNReal.rpow_two, ← ENNReal.rpow_two] at hb
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hb

end PlanarNikodym
