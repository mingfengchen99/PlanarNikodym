import PlanarNikodym.Analysis.Fourier.GlyzFinalFrequencyScale
import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricHolder

/-! Numerical comparisons between the literal frequency scale and
an eight-generation coarsening. Both the high-frequency and bounded
low-frequency cases have constants independent of the frequency. -/
noncomputable section
namespace PlanarNikodym

theorem glyz_exact_frequency_scale_pos {k : ℕ} {r : ℝ} (hr : 0 < r) :
    0 < r ^ (-(1 / (k : ℝ))) := Real.rpow_pos_of_pos hr _

theorem glyz_exact_frequency_scale_le_one {k : ℕ} {r : ℝ} (hr : 1 ≤ r) :
    r ^ (-(1 / (k : ℝ))) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hr
    (neg_nonpos.mpr (one_div_nonneg.mpr (Nat.cast_nonneg k)))

theorem glyz_exact_frequency_scale_coarse_bounds {k : ℕ} (hk : 0 < k)
    {r : ℝ} {N : ℕ} (hl : (2 : ℝ) ^ N ≤ r) (hu : r ≤ (2 : ℝ) ^ (N + 1))
    (hF : 8 ≤ glyzVariableFinalDepth k N) :
    128 * r ^ (-(1 / (k : ℝ))) ≤ glyzDyadicScale (glyzVariableFinalDepth k N - 8) ∧
      glyzDyadicScale (glyzVariableFinalDepth k N - 8) ≤
        512 * r ^ (-(1 / (k : ℝ))) := by
  obtain ⟨h₁, h₂⟩ := glyz_final_frequency_scale_comparable hk hl hu
  exact glyz_eight_coarser_scale_bounds (by linarith) h₂ hF

theorem glyz_exact_frequency_scale_low_bound {k : ℕ} (hk : 0 < k)
    {r : ℝ} {N : ℕ} (hl : (2 : ℝ) ^ N ≤ r) (hu : r ≤ (2 : ℝ) ^ (N + 1))
    (hF : glyzVariableFinalDepth k N < 8) :
    (1 / 256 : ℝ) ≤ r ^ (-(1 / (k : ℝ))) :=
  glyz_small_final_scale_lower (glyz_final_frequency_scale_comparable hk hl hu).2 hF

theorem glyz_sharp_power_loss_nonneg {k : ℕ} (hk : 0 < k) {p : ℝ}
    (hp : glyzCriticalExponent k ≤ p) :
    0 ≤ p - glyzCriticalExponent k / 2 - 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcrit : 2 ≤ glyzCriticalExponent k := by
    dsimp only [glyzCriticalExponent]
    nlinarith
  linarith

theorem glyz_sharp_power_exponent_nonneg {k : ℕ} (hk : 0 < k) {p ε : ℝ}
    (hp : glyzCriticalExponent k ≤ p) (hε : 0 ≤ ε) :
    0 ≤ (p - glyzCriticalExponent k / 2 - 1) / (k : ℝ) + ε :=
  add_nonneg (div_nonneg (glyz_sharp_power_loss_nonneg hk hp) (Nat.cast_nonneg k)) hε

theorem glyz_sharp_power_exponent_pos {k : ℕ} (hk : 0 < k) {p ε : ℝ}
    (hp : glyzCriticalExponent k ≤ p) (hε : 0 < ε) :
    0 < (p - glyzCriticalExponent k / 2 - 1) / (k : ℝ) + ε :=
  add_pos_of_nonneg_of_pos
    (div_nonneg (glyz_sharp_power_loss_nonneg hk hp) (Nat.cast_nonneg k)) hε

end PlanarNikodym
