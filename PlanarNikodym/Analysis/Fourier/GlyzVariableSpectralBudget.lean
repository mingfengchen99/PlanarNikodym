import PlanarNikodym.Analysis.Fourier.GlyzVariableDepthSchedule

/-! Actual numerical Fourier-thickening budget for the variable-scale
iteration. The fixed dyadic offset absorbs the radial and 2π constants. -/
noncomputable section
namespace PlanarNikodym

theorem glyz_dyadic_frequency_margin (n N d q Z : ℕ)
    (h : n * (d + q) + Z ≤ N) :
    (2 : ℝ) ^ Z ≤ (2 : ℝ) ^ N * glyzDyadicScale d ^ n * glyzDyadicScale q ^ n := by
  have hp : (2 : ℝ) ^ (Z + (d * n + q * n)) ≤ (2 : ℝ) ^ N :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have he : (2 : ℝ) ^ N * glyzDyadicScale d ^ n * glyzDyadicScale q ^ n =
      (2 : ℝ) ^ N / (2 : ℝ) ^ (d * n + q * n) := by
    simp only [glyzDyadicScale, inv_pow, pow_add, pow_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (d * n + q * n))).mpr
  simpa only [pow_add] using hp

theorem glyz_dyadic_curve_margin (n d q Z : ℕ) (h : n * q + Z ≤ d) :
    glyzDyadicScale d * (2 : ℝ) ^ Z ≤ glyzDyadicScale q ^ n := by
  have hb := glyz_dyadic_frequency_margin n d 0 q Z (by simpa using h)
  have hm := mul_le_mul_of_nonneg_left hb (glyzDyadicScale_pos d).le
  simpa only [glyzDyadicScale, pow_zero, inv_one, one_pow, mul_one, ← mul_assoc,
    inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ d ≠ 0), one_mul] using hm

/-- The final inequality is the genuine thickening requirement,
including its additive one and Fourier's 2π normalization. -/
theorem glyz_variable_spectral_budget (n N d q c Z : ℕ) {ζ rmin : ℝ}
    (hζ : 0 ≤ ζ) (hrmin : 0 < rmin)
    (hZ : ζ * N + c ≤ Z)
    (hc : 40 * Real.pi / rmin ≤ (2 : ℝ) ^ c)
    (hparent : n * q + Z ≤ d)
    (hfrequency : n * (d + q) + Z ≤ N) :
    let R := (2 : ℝ) ^ N * glyzDyadicScale d ^ n
    let α := R * glyzDyadicScale d
    let T := (2 : ℝ) ^ (ζ * N)
    1 + 2 * (1 + |α|) * T ≤
      (rmin / 4) * (R / (2 * Real.pi)) * glyzDyadicScale q ^ n := by
  let R := (2 : ℝ) ^ N * glyzDyadicScale d ^ n
  let α := R * glyzDyadicScale d
  let T := (2 : ℝ) ^ (ζ * N)
  let S := R * glyzDyadicScale q ^ n
  have hR : 0 < R := mul_pos (by positivity) (pow_pos (glyzDyadicScale_pos d) n)
  have hα : 0 ≤ α := mul_nonneg hR.le (glyzDyadicScale_pos d).le
  have hS : 0 ≤ S := mul_nonneg hR.le (pow_nonneg (glyzDyadicScale_pos q).le n)
  have hT : 1 ≤ T := Real.one_le_rpow (by norm_num) (by positivity)
  have hT2 : (2 : ℝ) ^ c * T ≤ (2 : ℝ) ^ Z := by
    dsimp [T]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hfirst : (2 : ℝ) ^ c * T ≤ S := hT2.trans (glyz_dyadic_frequency_margin n N d q Z hfrequency)
  have hsecond : (2 : ℝ) ^ c * α * T ≤ S := by
    have h := mul_le_mul_of_nonneg_left hT2 (mul_nonneg hR.le (glyzDyadicScale_pos d).le)
    have hmargin := mul_le_mul_of_nonneg_left (glyz_dyadic_curve_margin n d q Z hparent) hR.le
    dsimp [α, S]
    nlinarith
  have hleft : 1 + 2 * (1 + α) * T ≤ 5 * S / (2 : ℝ) ^ c := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ c)).mpr
    have hunit : (2 : ℝ) ^ c ≤ S := (le_mul_of_one_le_right (by positivity) hT).trans hfirst
    nlinarith
  have hc' : 5 / (2 : ℝ) ^ c ≤ rmin / (8 * Real.pi) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ c)
      (by positivity : (0 : ℝ) < 8 * Real.pi)).mpr
    have hcc := (div_le_iff₀ hrmin).mp hc
    nlinarith
  change 1 + 2 * (1 + |α|) * T ≤ _
  rw [abs_of_nonneg hα]
  calc
    _ ≤ 5 * S / (2 : ℝ) ^ c := hleft
    _ = (5 / (2 : ℝ) ^ c) * S := by ring
    _ ≤ (rmin / (8 * Real.pi)) * S := mul_le_mul_of_nonneg_right hc' hS
    _ = _ := by dsimp [S, R]; ring

/-- The same budget holds for every actual frequency above its dyadic lower bound. -/
theorem glyz_variable_spectral_budget_of_frequency (n N d q c Z : ℕ) {ζ rmin Λ : ℝ}
    (hΛ : (2 : ℝ) ^ N ≤ Λ)
    (hζ : 0 ≤ ζ) (hrmin : 0 < rmin)
    (hZ : ζ * N + c ≤ Z)
    (hc : 40 * Real.pi / rmin ≤ (2 : ℝ) ^ c)
    (hparent : n * q + Z ≤ d)
    (hfrequency : n * (d + q) + Z ≤ N) :
    let R := Λ * glyzDyadicScale d ^ n
    let α := R * glyzDyadicScale d
    let T := (2 : ℝ) ^ (ζ * N)
    1 + 2 * (1 + |α|) * T ≤
      (rmin / 4) * (R / (2 * Real.pi)) * glyzDyadicScale q ^ n := by
  let R := Λ * glyzDyadicScale d ^ n
  let α := R * glyzDyadicScale d
  let T := (2 : ℝ) ^ (ζ * N)
  let S := R * glyzDyadicScale q ^ n
  have hR : 0 < R := mul_pos (lt_of_lt_of_le (by positivity) hΛ)
    (pow_pos (glyzDyadicScale_pos d) n)
  have hα : 0 ≤ α := mul_nonneg hR.le (glyzDyadicScale_pos d).le
  have hS : 0 ≤ S := mul_nonneg hR.le (pow_nonneg (glyzDyadicScale_pos q).le n)
  have hT : 1 ≤ T := Real.one_le_rpow (by norm_num) (by positivity)
  have hT2 : (2 : ℝ) ^ c * T ≤ (2 : ℝ) ^ Z := by
    dsimp [T]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hfirst : (2 : ℝ) ^ c * T ≤ S := by
    apply hT2.trans
    apply (glyz_dyadic_frequency_margin n N d q Z hfrequency).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΛ (pow_nonneg (glyzDyadicScale_pos d).le n))
      (pow_nonneg (glyzDyadicScale_pos q).le n)
  have hsecond : (2 : ℝ) ^ c * α * T ≤ S := by
    have h := mul_le_mul_of_nonneg_left hT2 (mul_nonneg hR.le (glyzDyadicScale_pos d).le)
    have hmargin := mul_le_mul_of_nonneg_left (glyz_dyadic_curve_margin n d q Z hparent) hR.le
    dsimp [α, S]
    nlinarith
  have hleft : 1 + 2 * (1 + α) * T ≤ 5 * S / (2 : ℝ) ^ c := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ c)).mpr
    have hunit : (2 : ℝ) ^ c ≤ S := (le_mul_of_one_le_right (by positivity) hT).trans hfirst
    nlinarith
  have hc' : 5 / (2 : ℝ) ^ c ≤ rmin / (8 * Real.pi) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ c)
      (by positivity : (0 : ℝ) < 8 * Real.pi)).mpr
    have hcc := (div_le_iff₀ hrmin).mp hc
    nlinarith
  change 1 + 2 * (1 + |α|) * T ≤ _
  rw [abs_of_nonneg hα]
  calc
    _ ≤ 5 * S / (2 : ℝ) ^ c := hleft
    _ = (5 / (2 : ℝ) ^ c) * S := by ring
    _ ≤ (rmin / (8 * Real.pi)) * S := mul_le_mul_of_nonneg_right hc' hS
    _ = _ := by dsimp [S, R]; ring

/-- The radial offset is chosen before every frequency and every
scale, and therefore only changes the fixed constants. -/
theorem exists_glyz_variable_spectral_offset (rmin : ℝ) :
    ∃ c : ℕ, 40 * Real.pi / rmin ≤ (2 : ℝ) ^ c := by
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt (40 * Real.pi / rmin) (by norm_num : (1 : ℝ) < 2)
  exact ⟨c, hc.le⟩

end PlanarNikodym
