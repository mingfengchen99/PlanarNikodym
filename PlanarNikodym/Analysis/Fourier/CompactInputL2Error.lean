import PlanarNikodym.Analysis.Fourier.GlyzLocalizedParabolicSymbol
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Conversion of actual compact-frequency L¹ errors to L² errors.
The only constant is the square root of the frequency support measure. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem eLpNorm_one_le_two_of_support_subset
    {Y F : Type*} [MeasurableSpace Y] [NormedAddCommGroup F]
    {μ : Measure Y} {g : Y → F} (hg : AEStronglyMeasurable g μ)
    {J : Set Y} (hs : Function.support g ⊆ J) :
    eLpNorm g 1 μ ≤ eLpNorm g 2 μ * μ J ^ (1 / 2 : ℝ) := by
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict J) (p := 1) (q := 2) (by norm_num) hg.restrict
  simpa only [eLpNorm_restrict_eq_of_support_subset hs, Measure.restrict_apply_univ,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using hh

theorem integrable_of_memLp_two_support_finite
    {Y F : Type*} [MeasurableSpace Y] [NormedAddCommGroup F]
    {μ : Measure Y} {g : Y → F} (hg : MemLp g 2 μ)
    {J : Set Y} (hJ : μ J ≠ ∞) (hs : Function.support g ⊆ J) :
    Integrable g μ := by
  apply memLp_one_iff_integrable.mp
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  apply (eLpNorm_one_le_two_of_support_subset hg.aestronglyMeasurable hs).trans_lt
  exact ENNReal.mul_lt_top hg.eLpNorm_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ)

theorem integral_norm_le_sqrt_measure_mul_lpNorm_two
    {Y F : Type*} [MeasurableSpace Y] [NormedAddCommGroup F]
    {μ : Measure Y} {g : Y → F} (hg : MemLp g 2 μ)
    {J : Set Y} (hJ : μ J ≠ ∞) (hs : Function.support g ⊆ J) :
    (∫ y, ‖g y‖ ∂μ) ≤ Real.sqrt (μ J).toReal * lpNorm g 2 μ := by
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hg.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hJ))
    (eLpNorm_one_le_two_of_support_subset hg.aestronglyMeasurable hs)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    toReal_eLpNorm hg.aestronglyMeasurable,
    toReal_eLpNorm hg.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hg.aestronglyMeasurable,
    ← Real.sqrt_eq_rpow, mul_comm] at hh
  exact hh

end PlanarNikodym
