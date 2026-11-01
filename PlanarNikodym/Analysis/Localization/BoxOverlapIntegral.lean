import PlanarNikodym.Analysis.Localization.CoefficientBoxPartition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Bounded overlap controls the sum of actual unit-box norm powers,
without a factor equal to the number of boxes in the expanding domain. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Classical
namespace PlanarNikodym

theorem sum_setLIntegral_le_of_overlap {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (A : ι → Set X) (hA : ∀ i ∈ I, MeasurableSet (A i))
    (B : ℕ) (hB : ∀ x, (I.filter (fun i => x ∈ A i)).card ≤ B)
    (F : X → ℝ≥0∞) (hF : Measurable F) :
    (∑ i ∈ I, ∫⁻ x in A i, F x ∂μ) ≤ (B : ℝ≥0∞) * ∫⁻ x, F x ∂μ := by
  have hEq : ∀ i ∈ I, (∫⁻ x in A i, F x ∂μ) = ∫⁻ x, (A i).indicator F x ∂μ :=
    fun i hi => (lintegral_indicator (hA i hi) F).symm
  rw [Finset.sum_congr rfl hEq, ← lintegral_finsetSum I (fun i hi => hF.indicator (hA i hi)),
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top B)]
  apply lintegral_mono
  intro x
  change (∑ i ∈ I, (A i).indicator F x) ≤ (B : ℝ≥0∞) * F x
  have he : ∑ i ∈ I, (A i).indicator F x = ((I.filter (fun i => x ∈ A i)).card : ℝ≥0∞) * F x := by
    simp only [Set.indicator_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [he]
  exact mul_le_mul_left (by exact_mod_cast hB x) _

theorem sum_coefficientBox_lintegral_le {m : ℕ} (a : ℝ) (N : ℕ)
    (F : Aux m → ℝ≥0∞) (hF : Measurable F) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin m => Finset.range N),
      ∫⁻ x in tsupport (coefficientBoxCutoff a k), F x) ≤
        (3 ^ m : ℝ≥0∞) * ∫⁻ x, F x := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    sum_setLIntegral_le_of_overlap volume _ (fun k => tsupport (coefficientBoxCutoff a k))
      (fun _ _ => (isClosed_tsupport _).measurableSet) (3 ^ m)
      (coefficientBoxCutoff_overlap_le a N) F hF

end PlanarNikodym
