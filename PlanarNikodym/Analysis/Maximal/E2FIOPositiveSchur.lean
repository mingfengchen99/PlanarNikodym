import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual positive-kernel L² Schur argument used for the full FIO
TT* operator. This is an integral proof; there is no operator-bound input. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace PlanarNikodym
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem e2_lintegral_sq_le_mass_mul_sq (μ : Measure X) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) ^ (2 : ℕ) ≤ μ Set.univ * ∫⁻ x, f x ^ (2 : ℕ) ∂μ := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (aemeasurable_const (b := (1 : ℝ≥0∞))) hf.aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two, one_pow, lintegral_one] at hh
  have hh2 := pow_le_pow_left₀ (show (0 : ℝ≥0∞) ≤ ∫⁻ x, f x ∂μ from zero_le) hh 2
  simpa only [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] using hh2

theorem e2_weighted_lintegral_sq (μ : Measure X) {w f : X → ℝ≥0∞}
    (hw : Measurable w) (hf : Measurable f) :
    (∫⁻ x, w x * f x ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ x, w x ∂μ) * ∫⁻ x, w x * f x ^ (2 : ℕ) ∂μ := by
  have hh := e2_lintegral_sq_le_mass_mul_sq (μ.withDensity w) hf
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul μ hw hf,
    lintegral_withDensity_eq_lintegral_mul μ hw (hf.pow_const 2)] at hh
  exact hh

theorem e2_positive_kernel_l2_schur (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] {κ : X → Y → ℝ≥0∞} {f : Y → ℝ≥0∞}
    (hκ : Measurable (Function.uncurry κ)) (hf : Measurable f)
    (A B : ℝ≥0∞) (hrow : ∀ x, ∫⁻ y, κ x y ∂ν ≤ A)
    (hcol : ∀ y, ∫⁻ x, κ x y ∂μ ≤ B) :
    (∫⁻ x, (∫⁻ y, κ x y * f y ∂ν) ^ (2 : ℕ) ∂μ) ≤
      A * B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν := by
  have hprod : Measurable (fun z : X × Y => κ z.1 z.2 * f z.2 ^ (2 : ℕ)) :=
    hκ.mul ((hf.comp measurable_snd).pow_const _)
  calc
    _ ≤ ∫⁻ x, A * ∫⁻ y, κ x y * f y ^ (2 : ℕ) ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      exact (e2_weighted_lintegral_sq ν (hκ.comp (measurable_const.prodMk measurable_id)) hf).trans
        (mul_le_mul_left (hrow x) _)
    _ = A * ∫⁻ x, ∫⁻ y, κ x y * f y ^ (2 : ℕ) ∂ν ∂μ :=
      lintegral_const_mul A hprod.lintegral_prod_right
    _ = A * ∫⁻ y, ∫⁻ x, κ x y * f y ^ (2 : ℕ) ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hprod.aemeasurable]
    _ ≤ A * (B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν) := by
      gcongr
      calc
        _ = ∫⁻ y, (∫⁻ x, κ x y ∂μ) * f y ^ (2 : ℕ) ∂ν := by
          congr 1
          funext y
          exact lintegral_mul_const _ (hκ.comp (measurable_id.prodMk measurable_const))
        _ ≤ ∫⁻ y, B * f y ^ (2 : ℕ) ∂ν := lintegral_mono (fun y => mul_le_mul_left (hcol y) _)
        _ = _ := lintegral_const_mul B (hf.pow_const 2)
    _ = _ := (mul_assoc _ _ _).symm

end PlanarNikodym
