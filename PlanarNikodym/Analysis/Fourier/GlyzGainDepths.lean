import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants

/-! Dyadic depth arithmetic for the lower-degree gain. Rounding is
absorbed by a fixed inverse-radius factor, without altering the target
asymmetric exponent. -/
noncomputable section
open scoped NNReal ENNReal
namespace PlanarNikodym

theorem glyzDyadicDepth_mono (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    glyzDyadicDepth N a ≤ glyzDyadicDepth N b :=
  Nat.ceil_mono (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N))

theorem glyz_gain_depth_mul_le (l r N : ℕ) (hl : 0 < l)
    {β : ℝ} (hβ : 0 ≤ β) :
    glyzDyadicDepth N (((r : ℝ) + 1) / l * β) * l ≤
      glyzDyadicDepth N β * (r + 1) + l := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hβN : β * N ≤ (glyzDyadicDepth N β : ℝ) := Nat.le_ceil _
  have hc : 0 ≤ (((r : ℝ) + 1) / l * β) * N := by positivity
  have hceil : (glyzDyadicDepth N (((r : ℝ) + 1) / l * β) : ℝ) ≤
      (((r : ℝ) + 1) / l * β) * N + 1 :=
    (Nat.ceil_lt_add_one hc).le
  have he : ((((r : ℝ) + 1) / l * β) * N) * l =
      ((r : ℝ) + 1) * (β * N) := by field_simp
  have hmul := mul_le_mul_of_nonneg_right hceil hlR.le
  have hother := mul_le_mul_of_nonneg_left hβN (show 0 ≤ (r : ℝ) + 1 by positivity)
  have h : (glyzDyadicDepth N (((r : ℝ) + 1) / l * β) : ℝ) * l ≤
      (glyzDyadicDepth N β : ℝ) * ((r : ℝ) + 1) + l := by
    nlinarith
  exact_mod_cast h

theorem glyz_gain_inverse_radius_le (l r N : ℕ) (hl : 0 < l)
    {β : ℝ} (hβ : 0 ≤ β) :
    glyzDyadicScale (glyzDyadicDepth N β) ^ (r + 1) ≤
      (2 : ℝ) ^ l *
        glyzDyadicScale (glyzDyadicDepth N (((r : ℝ) + 1) / l * β)) ^ l := by
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (glyz_gain_depth_mul_le l r N hl hβ)
  rw [pow_add] at hpow
  have hdiv :
      (1 : ℝ) / (2 ^ (glyzDyadicDepth N β * (r + 1))) ≤
        2 ^ l / (2 ^ (glyzDyadicDepth N (((r : ℝ) + 1) / l * β) * l)) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)
  simpa only [glyzDyadicScale, inv_pow, ← pow_mul, div_eq_mul_inv, one_mul] using hdiv

end PlanarNikodym
