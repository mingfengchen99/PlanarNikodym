import PlanarNikodym.Analysis.Fourier.GlyzVariableDepthSchedule
import PlanarNikodym.Analysis.Fourier.GlyzDyadicRescaling
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Arbitrary positive frequency is reduced to a dyadic shell. The
actual rounded terminal depth gives intervals comparable to the
frequency-dependent scale, with constants independent of frequency. -/
noncomputable section
namespace PlanarNikodym

theorem exists_glyz_frequency_shell {r : ℝ} (hr : 1 ≤ r) :
    ∃ N : ℕ, (2 : ℝ) ^ N ≤ r ∧ r < (2 : ℝ) ^ (N + 1) :=
  exists_nat_pow_near hr (by norm_num)

theorem glyzVariableFinalDepth_integer_bounds {k : ℕ} (hk : 0 < k) (N : ℕ) :
    N ≤ k * glyzVariableFinalDepth k N ∧
      k * glyzVariableFinalDepth k N < N + k := by
  have hdiv := Nat.div_add_mod (N + k - 1) k
  have hmod := Nat.mod_lt (N + k - 1) hk
  unfold glyzVariableFinalDepth
  omega

theorem glyzVariableFinalDepth_real_bounds {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (N : ℝ) / k ≤ glyzVariableFinalDepth k N ∧
      (glyzVariableFinalDepth k N : ℝ) < (N : ℝ) / k + 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨hl, hu⟩ := glyzVariableFinalDepth_integer_bounds hk N
  have hlR : (N : ℝ) ≤ (k : ℝ) * glyzVariableFinalDepth k N := by exact_mod_cast hl
  have huR : (k : ℝ) * glyzVariableFinalDepth k N < (N : ℝ) + k := by exact_mod_cast hu
  constructor
  · exact (div_le_iff₀ hkR).mpr (by nlinarith)
  · have he : ((N : ℝ) / k) * k = N := div_mul_cancel₀ _ hkR.ne'
    nlinarith

theorem glyzDyadicScale_eq_rpow (N : ℕ) :
    glyzDyadicScale N = (2 : ℝ) ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rfl

theorem glyz_final_frequency_scale_comparable {k : ℕ} (hk : 0 < k)
    {r : ℝ} {N : ℕ} (hl : (2 : ℝ) ^ N ≤ r) (hu : r ≤ (2 : ℝ) ^ (N + 1)) :
    (1 / 2 : ℝ) * r ^ (-(1 / (k : ℝ))) ≤ glyzDyadicScale (glyzVariableFinalDepth k N) ∧
      glyzDyadicScale (glyzVariableFinalDepth k N) ≤ 2 * r ^ (-(1 / (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 < r := (pow_pos (by norm_num : (0 : ℝ) < 2) N).trans_le hl
  have hexp : -(1 / (k : ℝ)) ≤ 0 := neg_nonpos.mpr (one_div_nonneg.mpr hkR.le)
  have hp (j : ℕ) : ((2 : ℝ) ^ j) ^ (-(1 / (k : ℝ))) =
      (2 : ℝ) ^ (-(j : ℝ) / k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hrootl := Real.rpow_le_rpow_of_nonpos hr hu hexp
  have hrootu := Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num : (0 : ℝ) < 2) N) hl hexp
  rw [hp] at hrootl hrootu
  obtain ⟨hdepthl, hdepthu⟩ := glyzVariableFinalDepth_real_bounds hk N
  rw [glyzDyadicScale_eq_rpow]
  constructor
  · calc
      (1 / 2 : ℝ) * r ^ (-(1 / (k : ℝ))) ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(N : ℝ) / k) := by
        gcongr
      _ = (2 : ℝ) ^ (-(N : ℝ) / k - 1) := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        ring
      _ ≤ (2 : ℝ) ^ (-(glyzVariableFinalDepth k N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [neg_div]; linarith)
  · calc
      (2 : ℝ) ^ (-(glyzVariableFinalDepth k N : ℝ)) ≤
          (2 : ℝ) ^ (1 + (-((N + 1 : ℕ) : ℝ)) / k) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hinv : (1 : ℝ) / k ≤ 1 := (div_le_one hkR).mpr hk1
        simp only [Nat.cast_add, Nat.cast_one, neg_div, add_div]
        linarith
      _ = 2 * (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ) / (k : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      _ ≤ 2 * r ^ (-(1 / (k : ℝ))) := by gcongr

theorem exists_glyz_final_frequency_scale {k : ℕ} (hk : 0 < k)
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ N : ℕ, (2 : ℝ) ^ N ≤ r ∧ r < (2 : ℝ) ^ (N + 1) ∧
      (1 / 2 : ℝ) * r ^ (-(1 / (k : ℝ))) ≤ glyzDyadicScale (glyzVariableFinalDepth k N) ∧
      glyzDyadicScale (glyzVariableFinalDepth k N) ≤ 2 * r ^ (-(1 / (k : ℝ))) := by
  obtain ⟨N, hl, hu⟩ := exists_glyz_frequency_shell hr
  exact ⟨N, hl, hu, glyz_final_frequency_scale_comparable hk hl hu.le⟩

theorem glyz_frequency_shell_positive_loss {r a : ℝ} {N : ℕ}
    (hl : (2 : ℝ) ^ N ≤ r) (ha : 0 ≤ a) :
    (2 : ℝ) ^ (a * N) ≤ r ^ a := by
  have h := Real.rpow_le_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N) hl ha
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  simpa only [mul_comm] using h

theorem glyz_frequency_shell_negative_loss {r a : ℝ} {N : ℕ}
    (hr : 0 < r) (hu : r ≤ (2 : ℝ) ^ (N + 1)) (ha : 0 ≤ a) :
    (2 : ℝ) ^ (-a * N) ≤ (2 : ℝ) ^ a * r ^ (-a) := by
  have h := Real.rpow_le_rpow_of_nonpos hr hu (neg_nonpos.mpr ha)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hh := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hh
  have he : a + ((N + 1 : ℕ) : ℝ) * (-a) = -a * (N : ℝ) := by push_cast; ring
  rwa [he] at hh

/-- Eight coarser generations leave room for whole standard smooth
supports while keeping the number of residue colors fixed. -/
theorem glyz_eight_coarser_scale_bounds {F : ℕ} {h : ℝ}
    (hl : h / 2 ≤ glyzDyadicScale F) (hu : glyzDyadicScale F ≤ 2 * h) (hF : 8 ≤ F) :
    128 * h ≤ glyzDyadicScale (F - 8) ∧ glyzDyadicScale (F - 8) ≤ 512 * h := by
  have he := glyzDyadicScale_add (F - 8) 8
  rw [Nat.sub_add_cancel hF] at he
  have h8 : glyzDyadicScale 8 = 1 / 256 := by norm_num [glyzDyadicScale]
  rw [h8] at he
  constructor <;> linarith

theorem glyz_small_final_scale_lower {F : ℕ} {h : ℝ}
    (hu : glyzDyadicScale F ≤ 2 * h) (hF : F < 8) : (1 / 256 : ℝ) ≤ h := by
  have hF7 : F ≤ 7 := by omega
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show -(7 : ℝ) ≤ -(F : ℝ) by exact_mod_cast (neg_le_neg (show (F : ℤ) ≤ 7 by exact_mod_cast hF7)))
  have hpow' : glyzDyadicScale 7 ≤ glyzDyadicScale F := by
    simpa only [glyzDyadicScale_eq_rpow, Nat.cast_ofNat] using hpow
  have h7 : glyzDyadicScale 7 = 1 / 128 := by norm_num [glyzDyadicScale]
  rw [h7] at hpow'
  linarith

end PlanarNikodym
