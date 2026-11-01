import PlanarNikodym.Analysis.Maximal.E2SeeleyFiniteMoments

/-! Scaled, actual moment-correcting blocks. Enlarging the negative nodes
preserves the top moment while making every lower weighted absolute mass
arbitrarily small. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

def e2SeeleyScaledNode (n : ℕ) (R : ℝ) (k : Fin (n + 1)) : ℝ := R * e2SeeleyNode n k

def e2SeeleyScaledCoefficient (n : ℕ) (e R : ℝ) (k : Fin (n + 1)) : ℝ :=
  (e / R ^ n) * e2SeeleyMomentCoefficient n k

def e2SeeleyBlockMass (n j : ℕ) : ℝ :=
  ∑ k : Fin (n + 1), |e2SeeleyMomentCoefficient n k| * |e2SeeleyNode n k| ^ j

theorem e2SeeleyBlockMass_nonneg (n j : ℕ) : 0 ≤ e2SeeleyBlockMass n j := by
  unfold e2SeeleyBlockMass
  positivity

theorem e2SeeleyScaledCoefficient_moment (n j : ℕ) (hj : j ≤ n) (e R : ℝ) :
    ∑ k : Fin (n + 1), e2SeeleyScaledCoefficient n e R k * (e2SeeleyScaledNode n R k) ^ j =
      (e * R ^ j / R ^ n) * (if j = n then 1 else 0) := by
  calc
    _ = (e * R ^ j / R ^ n) *
        ∑ k : Fin (n + 1), e2SeeleyMomentCoefficient n k * (e2SeeleyNode n k) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [e2SeeleyScaledCoefficient, e2SeeleyScaledNode, mul_pow]
      ring
    _ = _ := by rw [e2SeeleyMomentCoefficient_moment n j hj]

theorem e2SeeleyScaledCoefficient_low (n j : ℕ) (hj : j < n) (e R : ℝ) :
    ∑ k : Fin (n + 1), e2SeeleyScaledCoefficient n e R k * (e2SeeleyScaledNode n R k) ^ j = 0 := by
  rw [e2SeeleyScaledCoefficient_moment n j hj.le, if_neg (Nat.ne_of_lt hj), mul_zero]

theorem e2SeeleyScaledCoefficient_top (n : ℕ) (e R : ℝ) (hR : R ≠ 0) :
    ∑ k : Fin (n + 1), e2SeeleyScaledCoefficient n e R k * (e2SeeleyScaledNode n R k) ^ n = e := by
  rw [e2SeeleyScaledCoefficient_moment n n le_rfl, if_pos rfl, mul_one,
    mul_div_cancel_right₀ e (pow_ne_zero n hR)]

theorem e2SeeleyScaledCoefficient_absolute_mass (n j : ℕ) (e R : ℝ) (hR : 0 < R) :
    ∑ k : Fin (n + 1), |e2SeeleyScaledCoefficient n e R k| * |e2SeeleyScaledNode n R k| ^ j =
      (|e| * e2SeeleyBlockMass n j) * (R ^ j / R ^ n) := by
  unfold e2SeeleyBlockMass
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [e2SeeleyScaledCoefficient, e2SeeleyScaledNode, abs_mul, abs_div, abs_pow,
    abs_of_pos hR, mul_pow]
  ring

def e2SeeleyBlockMassBound (n : ℕ) : ℝ := 1 + ∑ j ∈ Finset.range n, e2SeeleyBlockMass n j

theorem e2SeeleyBlockMassBound_pos (n : ℕ) : 0 < e2SeeleyBlockMassBound n := by
  have hh : 0 ≤ ∑ j ∈ Finset.range n, e2SeeleyBlockMass n j :=
    Finset.sum_nonneg (fun j _ => e2SeeleyBlockMass_nonneg n j)
  unfold e2SeeleyBlockMassBound
  linarith

theorem e2SeeleyBlockMass_le_bound (n j : ℕ) (hj : j < n) :
    e2SeeleyBlockMass n j ≤ e2SeeleyBlockMassBound n := by
  have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.range n) =>
    e2SeeleyBlockMass_nonneg n k) (Finset.mem_range.mpr hj)
  unfold e2SeeleyBlockMassBound
  linarith

def e2SeeleyBlockScale (n : ℕ) (e : ℝ) : ℝ :=
  max ((n : ℝ) + 1) (max 1 ((2 : ℝ) ^ n * (|e| * e2SeeleyBlockMassBound n + 1)))

theorem e2SeeleyBlockScale_ge_index (n : ℕ) (e : ℝ) : (n : ℝ) + 1 ≤ e2SeeleyBlockScale n e :=
  le_max_left _ _

theorem e2SeeleyBlockScale_ge_one (n : ℕ) (e : ℝ) : 1 ≤ e2SeeleyBlockScale n e :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem e2SeeleyBlockScale_pos (n : ℕ) (e : ℝ) : 0 < e2SeeleyBlockScale n e :=
  zero_lt_one.trans_le (e2SeeleyBlockScale_ge_one n e)

theorem e2SeeleyBlockScale_mass (n : ℕ) (e : ℝ) :
    (2 : ℝ) ^ n * (|e| * e2SeeleyBlockMassBound n + 1) ≤ e2SeeleyBlockScale n e :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- All lower-order absolute moments of the actual scaled block are
bounded by a geometric sequence, independently of its required top error. -/
theorem e2SeeleyScaledCoefficient_lower_mass (n j : ℕ) (hj : j < n) (e : ℝ) :
    ∑ k : Fin (n + 1), |e2SeeleyScaledCoefficient n e (e2SeeleyBlockScale n e) k| *
      |e2SeeleyScaledNode n (e2SeeleyBlockScale n e) k| ^ j ≤ ((2 : ℝ) ^ n)⁻¹ := by
  let R := e2SeeleyBlockScale n e
  have hR : 0 < R := e2SeeleyBlockScale_pos n e
  have hR1 : 1 ≤ R := e2SeeleyBlockScale_ge_one n e
  rw [e2SeeleyScaledCoefficient_absolute_mass n j e R hR]
  have hpow : R ^ j * R ≤ R ^ n := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ hR1 (Nat.succ_le_of_lt hj)
  have hratio : R ^ j / R ^ n ≤ 1 / R := by
    apply (div_le_div_iff₀ (pow_pos hR n) hR).mpr
    simpa only [one_mul] using hpow
  have hmass : (|e| * e2SeeleyBlockMassBound n) * (2 : ℝ) ^ n ≤ R := by
    have hh := e2SeeleyBlockScale_mass n e
    have ht : 0 ≤ (2 : ℝ) ^ n := by positivity
    nlinarith
  calc
    _ ≤ (|e| * e2SeeleyBlockMass n j) * (1 / R) :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg (abs_nonneg _) (e2SeeleyBlockMass_nonneg n j))
    _ ≤ (|e| * e2SeeleyBlockMassBound n) * (1 / R) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (e2SeeleyBlockMass_le_bound n j hj)
        (abs_nonneg _)) (by positivity)
    _ ≤ _ := by
      rw [mul_one_div, ← one_div]
      exact (div_le_div_iff₀ hR (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr (by simpa using hmass)

end PlanarNikodym
