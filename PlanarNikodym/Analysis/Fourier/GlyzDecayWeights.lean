import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Convolution

/-! Positive polynomial-decay weights in arbitrary finite dimension.
The exponent is a natural number, sufficient for the GLYZ v3 construction. -/

noncomputable section
open Set MeasureTheory

namespace PlanarNikodym

def glyzDecayWeight {n : ℕ} (A : ℕ) (x : Base n) : ℝ :=
  (max 1 ‖x‖ ^ A)⁻¹

theorem glyzDecayWeight_pos {n : ℕ} (A : ℕ) (x : Base n) :
    0 < glyzDecayWeight A x := by
  unfold glyzDecayWeight
  positivity

theorem continuous_glyzDecayWeight {n : ℕ} (A : ℕ) :
    Continuous (glyzDecayWeight (n := n) A) := by
  unfold glyzDecayWeight
  exact ((continuous_const.max continuous_norm).pow A).inv₀
    (fun x => ne_of_gt (by positivity))

theorem glyzDecayWeight_le_one {n : ℕ} (A : ℕ) (x : Base n) :
    glyzDecayWeight A x ≤ 1 := by
  apply (inv_le_one₀ (by positivity : 0 < max (1 : ℝ) ‖x‖ ^ A)).mpr
  exact one_le_pow₀ (le_max_left _ _)

theorem glyzDecayWeight_le_japanese {n : ℕ} (A : ℕ) (x : Base n) :
    glyzDecayWeight A x ≤ 2 ^ A * (1 + ‖x‖) ^ (-(A : ℝ)) := by
  have hm : 0 < max (1 : ℝ) ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hx : 0 < 1 + ‖x‖ := by positivity
  rw [Real.rpow_neg (le_of_lt hx), Real.rpow_natCast]
  change (max 1 ‖x‖ ^ A)⁻¹ ≤ 2 ^ A * ((1 + ‖x‖) ^ A)⁻¹
  have hb : 1 + ‖x‖ ≤ 2 * max (1 : ℝ) ‖x‖ := by
    linarith [le_max_left (1 : ℝ) ‖x‖, le_max_right (1 : ℝ) ‖x‖]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖) hb A
  rw [mul_pow] at hpow
  have he : (1 : ℝ) / max 1 ‖x‖ ^ A ≤ (2 : ℝ) ^ A / (1 + ‖x‖) ^ A :=
    (div_le_div_iff₀ (pow_pos hm A) (pow_pos hx A)).mpr (by simpa using hpow)
  simpa only [one_div, div_eq_mul_inv, one_mul] using he

theorem integrable_glyzDecayWeight {n A : ℕ} (hA : n < A) :
    Integrable (glyzDecayWeight (n := n) A) := by
  have hr : (Module.finrank ℝ (Base n) : ℝ) < (A : ℝ) := by
    simpa [Module.finrank_pi_fintype] using (show (n : ℝ) < (A : ℝ) by exact_mod_cast hA)
  apply ((integrable_one_add_norm (E := Base n) (μ := volume) hr).const_mul
    ((2 : ℝ) ^ A)).mono'
    (continuous_glyzDecayWeight A).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x =>
    (abs_of_pos (glyzDecayWeight_pos A x)).trans_le (glyzDecayWeight_le_japanese A x)

def glyzWeightExponent (n : ℕ) : ℕ := n * (n + 1) + n + 1

theorem glyzWeightExponent_gt_dim (n : ℕ) : n < glyzWeightExponent n := by
  unfold glyzWeightExponent
  omega

theorem glyzWeightExponent_ge_homogeneous (n : ℕ) :
    n * (n + 1) / 2 ≤ glyzWeightExponent n := by
  unfold glyzWeightExponent
  omega

/-- The two-region estimate in GLYZ Appendix A.1. The hypothesis on the
contraction and density is verified below for moment dilations. -/
theorem glyzDecayWeight_two_region {n A : ℕ} (T : Base n →ₗ[ℝ] Base n)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hpow : δ ^ A ≤ c)
    (hT : ∀ z, ‖T z‖ ≤ δ * ‖z‖) (x y : Base n) :
    glyzDecayWeight A (x - y) * (c * glyzDecayWeight A (T y)) ≤
      2 ^ A * (c * glyzDecayWeight A (T x)) *
        (glyzDecayWeight A (x - y) + c * glyzDecayWeight A (T y)) := by
  let u := max (1 : ℝ) ‖T x‖
  let v := max (1 : ℝ) ‖T y‖
  let z := max (1 : ℝ) ‖x - y‖
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hv : 0 < v := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hwx : 0 ≤ glyzDecayWeight A (T x) := (glyzDecayWeight_pos _ _).le
  have hwy : 0 ≤ glyzDecayWeight A (T y) := (glyzDecayWeight_pos _ _).le
  have hwz : 0 ≤ glyzDecayWeight A (x - y) := (glyzDecayWeight_pos _ _).le
  by_cases h : u ≤ 2 * v
  · have hp := pow_le_pow_left₀ hu.le h A
    rw [mul_pow] at hp
    have hh : glyzDecayWeight A (T y) ≤ 2 ^ A * glyzDecayWeight A (T x) := by
      change (v ^ A)⁻¹ ≤ 2 ^ A * (u ^ A)⁻¹
      have hh : (1 : ℝ) / v ^ A ≤ 2 ^ A / u ^ A :=
        (div_le_div_iff₀ (pow_pos hv A) (pow_pos hu A)).mpr (by simpa using hp)
      simpa only [one_div, div_eq_mul_inv, one_mul] using hh
    calc
      _ ≤ glyzDecayWeight A (x - y) * (c * (2 ^ A * glyzDecayWeight A (T x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hc) hwz
      _ = 2 ^ A * (c * glyzDecayWeight A (T x)) * glyzDecayWeight A (x - y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hc hwy))
        (by positivity)
  · have hlarge : 1 < u := by
      have := le_max_left (1 : ℝ) ‖T y‖
      dsimp [v] at *
      linarith
    have he : u = ‖T x‖ := by
      apply max_eq_right
      exact ((lt_max_iff.mp hlarge).resolve_left (lt_irrefl _)).le
    have htri : u ≤ δ * ‖x - y‖ + v := by
      rw [he]
      calc
        ‖T x‖ = ‖T (x - y) + T y‖ := by rw [map_sub, sub_add_cancel]
        _ ≤ ‖T (x - y)‖ + ‖T y‖ := norm_add_le _ _
        _ ≤ δ * ‖x - y‖ + v := add_le_add (hT _) (le_max_right _ _)
    have hnorm : u ≤ 2 * δ * z := by
      have hz' : ‖x - y‖ ≤ z := le_max_right _ _
      have := mul_le_mul_of_nonneg_left hz' hδ
      linarith
    have hp := pow_le_pow_left₀ hu.le hnorm A
    simp only [mul_pow] at hp
    have hp' : u ^ A ≤ 2 ^ A * c * z ^ A := hp.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (pow_nonneg hz.le A))
    have hh : glyzDecayWeight A (x - y) ≤ 2 ^ A * (c * glyzDecayWeight A (T x)) := by
      change (z ^ A)⁻¹ ≤ 2 ^ A * (c * (u ^ A)⁻¹)
      have : (1 : ℝ) / z ^ A ≤ (2 ^ A * c) / u ^ A :=
        (div_le_div_iff₀ (pow_pos hz A) (pow_pos hu A)).mpr (by simpa using hp')
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc] using this
    calc
      _ ≤ (2 ^ A * (c * glyzDecayWeight A (T x))) * (c * glyzDecayWeight A (T y)) :=
        mul_le_mul_of_nonneg_right hh (mul_nonneg hc hwy)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hwz) (by positivity)

end PlanarNikodym
