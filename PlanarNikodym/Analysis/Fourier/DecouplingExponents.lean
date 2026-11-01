import Mathlib.Analysis.MeanInequalities

/-! The finite sequence norm conversion and exponent bookkeeping in
conic decoupling. These statements supply no Fourier decoupling gain. -/
noncomputable section
open scoped BigOperators ENNReal
namespace PlanarNikodym

/-- Degree `n` corresponds to `d + 1` in Lemma 2.3. -/
def coneDecouplingExponent (n : ℕ) (p : ℝ) : ℝ :=
  (1 - 1 / p - (n : ℝ) * (n + 1) / (2 * p)) / n

theorem coneDecouplingExponent_split (n : ℕ) (p : ℝ) :
    coneDecouplingExponent n p =
      (1 / 2 - (n : ℝ) * (n + 1) / (2 * p)) / n + (1 / 2 - 1 / p) / n := by
  unfold coneDecouplingExponent
  ring

theorem coneDecouplingExponent_critical {n : ℕ} (hn : 0 < n) :
    coneDecouplingExponent n ((n : ℝ) * (n + 1)) =
      (1 / 2 - 1 / ((n : ℝ) * (n + 1))) / n := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold coneDecouplingExponent
  field_simp
  ring

/-- Hölder's sequence conversion, including empty sums and infinite
entries. This is the precise cardinality loss in passing from an ℓ²
right hand side to the ℓp right hand side used by Lemma 2.3. -/
theorem finite_l2_le_card_mul_lp {ι : Type*} (s : Finset ι)
    (a : ι → ℝ≥0∞) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i ∈ s, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (s.card : ℝ≥0∞) ^ (1 / 2 - 1 / p) * (∑ i ∈ s, a i ^ p) ^ (1 / p) := by
  have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hq : 1 ≤ p / 2 := by linarith
  have h := ENNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => a i ^ (2 : ℝ)) hq
  have h' := ENNReal.rpow_le_rpow h (show 0 ≤ 1 / p by positivity)
  have h2 : (2 : ℝ) * (p / 2) = p := by ring
  have h3 : p / 2 * (1 / p) = 1 / 2 := by field_simp
  have h4 : (p / 2 - 1) * (1 / p) = 1 / 2 - 1 / p := by field_simp
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p by positivity),
    ← ENNReal.rpow_mul, h2, h3, h4] using h'

theorem coneDecoupling_frequency_factors {n : ℕ} {R : ℝ} (hR : 0 < R) (p : ℝ) :
    R ^ ((1 / 2 - (n : ℝ) * (n + 1) / (2 * p)) / n) *
      R ^ ((1 / 2 - 1 / p) / n) = R ^ coneDecouplingExponent n p := by
  rw [← Real.rpow_add hR, coneDecouplingExponent_split]

end PlanarNikodym
