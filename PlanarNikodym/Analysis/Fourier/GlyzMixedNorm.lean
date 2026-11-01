import PlanarNikodym.Analysis.Fourier.GlyzWeightedHolder

/-! Finite Minkowski inequalities for the actual nonnegative integrals
in the lower-degree argument. No finiteness assumption on the integrals
is needed; in particular the empty family and infinite values are covered. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem glyz_lintegral_sum_minkowski {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (F : ι → α → ℝ≥0∞)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ x, (∑ i ∈ s, F i x) ^ q ∂μ) ^ (1 / q) ≤
      ∑ i ∈ s, (∫⁻ x, F i x ^ q ∂μ) ^ (1 / q) := by
  classical
  have hq0 : 0 < q := by linarith
  induction s using Finset.induction_on with
  | empty => simp [hq0]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs : ∀ j ∈ s, AEMeasurable (F j) μ := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have h := ENNReal.lintegral_Lp_add_le (hF i (Finset.mem_insert_self _ _))
      (Finset.aemeasurable_sum s hs) hq
    simp only [Pi.add_apply, Finset.sum_apply] at h
    exact h.trans (add_le_add_right (ih hs) _)

/-- The powered form of `L^p(ℓ²) ≤ ℓ²(L^p)`, applied to local
`p`-power integrals `U i`. The outer measure can already contain every
weight and every auxiliary translation in the slicing argument. -/
theorem glyz_lintegral_mixed_l2 {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (U : ι → α → ℝ≥0∞)
    (hU : ∀ i ∈ s, AEMeasurable (U i) μ) {p : ℝ} (hp : 2 ≤ p) :
    (∫⁻ x, (∑ i ∈ s, U i x ^ (2 / p)) ^ (p / 2) ∂μ) ≤
      (∑ i ∈ s, (∫⁻ x, U i x ∂μ) ^ (2 / p)) ^ (p / 2) := by
  have hp0 : 0 < p := by linarith
  have he : 2 / p * (p / 2) = 1 := by field_simp
  have h := glyz_lintegral_sum_minkowski μ s (fun i x => U i x ^ (2 / p))
    (fun i hi => (hU i hi).pow_const _) (by linarith : 1 ≤ p / 2)
  simp only [← ENNReal.rpow_mul, he, ENNReal.rpow_one] at h
  have h' := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ p / 2)
  have he' : 1 / (p / 2) = 2 / p := by field_simp
  simpa only [he', ← ENNReal.rpow_mul, he, ENNReal.rpow_one] using h'

/-- The same exchange with an arbitrary measurable density. This is
the precise weighted mixed-norm step used after local slice decoupling. -/
theorem glyz_lintegral_weighted_mixed_l2 {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (w : α → ℝ≥0∞) (U : ι → α → ℝ≥0∞)
    (hw : Measurable w) (hU : ∀ i ∈ s, Measurable (U i)) {p : ℝ} (hp : 2 ≤ p) :
    (∫⁻ x, w x * (∑ i ∈ s, U i x ^ (2 / p)) ^ (p / 2) ∂μ) ≤
      (∑ i ∈ s, (∫⁻ x, w x * U i x ∂μ) ^ (2 / p)) ^ (p / 2) := by
  have h := glyz_lintegral_mixed_l2 (μ.withDensity w) s U
    (fun i hi => (hU i hi).aemeasurable) hp
  have hsum : Measurable (fun x => (∑ i ∈ s, U i x ^ (2 / p)) ^ (p / 2)) :=
    (Finset.measurable_sum s (fun i hi => (hU i hi).pow_const _)).pow_const _
  rw [lintegral_withDensity_eq_lintegral_mul μ hw hsum] at h
  have he (i : ι) (hi : i ∈ s) := lintegral_withDensity_eq_lintegral_mul μ hw (hU i hi)
  convert h using 2
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i hi]
  rfl

end PlanarNikodym
