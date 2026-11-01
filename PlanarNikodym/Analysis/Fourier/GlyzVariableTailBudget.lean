import PlanarNikodym.Analysis.Fourier.GlyzVariableSpectralBudget

/-! Arbitrary decay orders for the actual spectral cutoff. Every fixed
polynomial loss is absorbed by choosing the integration-by-parts order
before the dyadic frequency. -/
noncomputable section
namespace PlanarNikodym

/-- The multiplier parameter is at most the original frequency whenever
the parent width is at most one. -/
theorem glyz_variable_alpha_le_frequency (n d : ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    |Λ * glyzDyadicScale d ^ (n + 1)| ≤ Λ := by
  have hd : 0 ≤ glyzDyadicScale d := (glyzDyadicScale_pos d).le
  have hd1 : glyzDyadicScale d ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  rw [abs_of_nonneg (mul_nonneg hΛ (pow_nonneg hd _))]
  exact mul_le_of_le_one_right hΛ (pow_le_one₀ hd hd1)

/-- The order M is uniform in N and in the multiplier parameter. B may
include all fixed Jacobian, domain-volume, and inverse-scale losses. -/
theorem exists_glyz_variable_tail_order (a : ℕ) {ζ : ℝ} (hζ : 0 < ζ)
    (B Q : ℝ) :
    ∃ M : ℕ, ∀ N : ℕ, ∀ α : ℝ, |α| ≤ (2 : ℝ) ^ (N + 1) →
      (2 : ℝ) ^ (B * N) * (1 + |α|) ^ a *
        ((2 : ℝ) ^ (ζ * N)) ^ (-(M : ℝ)) ≤
          (2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ (-Q * N) := by
  let M := ⌈((a : ℝ) + B + Q) / ζ⌉₊
  have hM : (a : ℝ) + B + Q ≤ ζ * M := by
    have hc := Nat.le_ceil (((a : ℝ) + B + Q) / ζ)
    simpa [M, mul_comm] using (div_le_iff₀ hζ).mp hc
  refine ⟨M, fun N α hα => ?_⟩
  have h2 : 1 ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
  have hbase : 1 + |α| ≤ (2 : ℝ) ^ (N + 2) := by
    rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
    linarith
  have hpow : (1 + |α|) ^ a ≤ (2 : ℝ) ^ ((N + 2) * a) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase a
  have hpre := mul_le_mul_of_nonneg_left hpow
    (by positivity : (0 : ℝ) ≤ 2 ^ (B * N))
  have hfull := mul_le_mul_of_nonneg_right hpre
    (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (ζ * N)) ^ (-(M : ℝ)))
  apply hfull.trans
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  have hMN := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

end PlanarNikodym
