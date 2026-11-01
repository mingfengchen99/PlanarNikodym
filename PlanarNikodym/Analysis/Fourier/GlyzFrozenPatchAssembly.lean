import PlanarNikodym.Analysis.Fourier.GlyzRawKernel
import PlanarNikodym.Analysis.Fourier.GlyzFullParameterCoordinates

/-! Finite output-patch assembly with explicit constants. Frozen-time
cutoffs multiply the original extension outside its input integral. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_finite_output_patch_assembly
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] (μ : Measure X)
    (F : X → ℂ) (ψ : ι → X → ℂ) {p : ℝ} (hp : 1 ≤ p)
    (hpart : ∀ x, ∑ i, ψ i x * F x = F x)
    (hm : ∀ i, Measurable (fun x => ‖ψ i x * F x‖ₑ ^ p))
    (D e : ι → ℝ≥0∞) (B : ℝ≥0∞)
    (hpatch : ∀ i, (∫⁻ x, ‖ψ i x * F x‖ₑ ^ p ∂μ) ≤ D i * B + e i) :
    (∫⁻ x, ‖F x‖ₑ ^ p ∂μ) ≤
      (Fintype.card ι : ℝ≥0∞) ^ (p - 1) * ((∑ i, D i) * B + ∑ i, e i) := by
  classical
  calc
    _ ≤ ∫⁻ x, (Fintype.card ι : ℝ≥0∞) ^ (p - 1) *
        ∑ i, ‖ψ i x * F x‖ₑ ^ p ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      conv_lhs => rw [← hpart x]
      have h := ENNReal.rpow_sum_le_const_mul_sum_rpow Finset.univ
        (fun i => ‖ψ i x * F x‖ₑ) hp
      exact (ENNReal.rpow_le_rpow (enorm_sum_le _ _) (zero_le_one.trans hp)).trans
        (by simpa only [Finset.card_univ] using h)
    _ = (Fintype.card ι : ℝ≥0∞) ^ (p - 1) *
        ∑ i, ∫⁻ x, ‖ψ i x * F x‖ₑ ^ p ∂μ := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i hi => hm i),
        lintegral_finsetSum _ (fun i hi => hm i)]
    _ ≤ (Fintype.card ι : ℝ≥0∞) ^ (p - 1) * ∑ i, (D i * B + e i) := by
      gcongr with i hi
      exact hpatch i
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]

/-- A chart cutoff bounded by one cannot enlarge any original child
norm; no new amplitude is introduced on the right hand side. -/
theorem glyz_output_cutoff_power_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ : X → ℝ) (F : X → ℂ) (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ‖(ρ x : ℂ) * F x‖ₑ ^ p ∂μ) ≤ ∫⁻ x, ‖F x‖ₑ ^ p ∂μ := by
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ hp
  have hb : ‖(ρ x : ℂ) * F x‖ ≤ ‖F x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ x).1]
    exact (mul_le_mul_of_nonneg_right (hρ x).2 (norm_nonneg _)).trans_eq (one_mul _)
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hb

/-- A smaller frozen chart patch is controlled by the chart cutoff
which is identically one on its support. -/
theorem glyz_output_patch_dominated_in_chart {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ψ ρ : X → ℝ) (F : X → ℂ) (S : Set X)
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hs : Function.support ψ ⊆ S)
    (hρ : ∀ x, ψ x ≠ 0 → ρ x = 1) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖(ψ x : ℂ) * F x‖ₑ ^ p ∂μ) ≤
      ∫⁻ x in S, ‖(ρ x : ℂ) * F x‖ₑ ^ p ∂μ := by
  have hs' : Function.support (fun x => ‖(ψ x : ℂ) * F x‖ₑ ^ p) ⊆ S := by
    intro x hx
    apply hs
    intro hz
    exact hx (by simp only [hz, Complex.ofReal_zero, zero_mul, enorm_zero,
      ENNReal.zero_rpow_of_pos hp])
  rw [← setLIntegral_eq_of_support_subset hs']
  apply lintegral_mono
  intro x
  dsimp only
  by_cases hz : ψ x = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul, enorm_zero,
      ENNReal.zero_rpow_of_pos hp, zero_le]
  · rw [hρ x hz, Complex.ofReal_one, one_mul]
    apply ENNReal.rpow_le_rpow _ hp.le
    have hn : ‖(ψ x : ℂ) * F x‖ ≤ ‖F x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψ x).1]
      exact (mul_le_mul_of_nonneg_right (hψ x).2 (norm_nonneg _)).trans_eq (one_mul _)
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hn

end PlanarNikodym
