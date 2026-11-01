import PlanarNikodym.Analysis.Fourier.GlyzVariableOffsetSchedule
import PlanarNikodym.Analysis.Fourier.GlyzVariableTailBudget

/-! Numerical bounds for the actual variable-coefficient iteration.
The output-volume factor is polynomial in the original frequency, and
the initial/final counting costs use an arbitrarily small exponent. -/
noncomputable section
open scoped ENNReal
namespace PlanarNikodym

/-- The exact output-volume loss in the global polynomial estimate is
bounded by a fixed power of the original dyadic frequency. -/
theorem glyz_variable_output_volume_le (k d N D : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hd : d ≤ N) :
    (((glyzDyadicScale d ^ k)⁻¹ * L + 1) ^ D) ≤
      (L + 1) ^ D * (2 : ℝ) ^ ((k * D : ℕ) * (N : ℝ)) := by
  have hpow : (2 : ℝ) ^ (d * k) ≤ (2 : ℝ) ^ (N * k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right k hd)
  have hone : 1 ≤ (2 : ℝ) ^ (N * k) := one_le_pow₀ (by norm_num)
  have hbase : (glyzDyadicScale d ^ k)⁻¹ * L + 1 ≤
      (L + 1) * (2 : ℝ) ^ (N * k) := by
    simp only [glyzDyadicScale, inv_pow, inv_inv, ← pow_mul]
    nlinarith [mul_le_mul_of_nonneg_right hpow hL]
  calc
    _ ≤ ((L + 1) * (2 : ℝ) ^ (N * k)) ^ D :=
      pow_le_pow_left₀ (by
        have := (glyzDyadicScale_pos d).le
        positivity) hbase D
    _ = _ := by
      have he : (2 : ℝ) ^ ((N * k) * D) =
          (2 : ℝ) ^ ((k * D : ℕ) * (N : ℝ)) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        ring
      rw [mul_pow, ← pow_mul, he]

/-- The terminal depth never exceeds N/k, including N below the
fixed Fourier offset. -/
theorem glyz_variable_terminal_real_bound (k N Z : ℕ) (hk : 0 < k) :
    (glyzVariableTerminalDepth k N Z : ℝ) ≤ (N : ℝ) / k := by
  have h := Nat.mul_div_le (N - Z) k
  have h' : k * glyzVariableTerminalDepth k N Z ≤ N := by
    unfold glyzVariableTerminalDepth
    omega
  apply (le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using h')

/-- Counting, scale increments, and the local epsilon loss are
budgeted before the frequency and fixed Fourier offset are chosen. -/
theorem exists_glyz_variable_total_exponent_budget (k : ℕ) (hk : 0 < k)
    {p σ ε : ℝ} (hp : 1 ≤ p) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ ζ η : ℝ, 0 < ζ ∧ 0 < η ∧ ∀ N c : ℕ,
      let Z := ⌈ζ * N⌉₊ + c
      let T := glyzVariableTerminalDepth k N Z
      let d := min T (2 * Z + 2 * k)
      (d : ℝ) * (p - 1) + (σ + η) * ((T - d : ℕ) : ℝ) +
        ((glyzVariableFinalDepth k N - T : ℕ) : ℝ) * (p - 1) ≤
          (σ / k + ε) * N + (2 * k + 3 * c + 5) * (p - 1) := by
  obtain ⟨ζ, hζ, hcount⟩ :=
    exists_glyz_variable_offset_counting_budget k hk hp (half_pos hε)
  let η := ε * k / 2
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  refine ⟨ζ, η, hζ, by dsimp [η]; positivity, fun N c => ?_⟩
  dsimp
  let Z := ⌈ζ * N⌉₊ + c
  let T := glyzVariableTerminalDepth k N Z
  let d := min T (2 * Z + 2 * k)
  have hd : d ≤ 2 * Z + 2 * k := min_le_right _ _
  have hsub : T - d ≤ T := Nat.sub_le _ _
  have hT := glyz_variable_terminal_real_bound k N Z hk
  have hdepth : ((T - d : ℕ) : ℝ) ≤ (N : ℝ) / k :=
    (show ((T - d : ℕ) : ℝ) ≤ (T : ℝ) by exact_mod_cast hsub).trans hT
  have hscale := mul_le_mul_of_nonneg_left hdepth
    (show 0 ≤ σ + η by dsimp [η]; positivity)
  have hi := mul_le_mul_of_nonneg_right
    (show (d : ℝ) ≤ (2 * Z + 2 * k : ℕ) by exact_mod_cast hd)
    (sub_nonneg.mpr hp)
  have hct := hcount N c
  have heq : (σ + η) * ((N : ℝ) / k) = (σ / k + ε / 2) * N := by
    dsimp [η]
    field_simp
  rw [heq] at hscale
  change (d : ℝ) * (p - 1) + (σ + η) * ((T - d : ℕ) : ℝ) +
    ((glyzVariableFinalDepth k N - T : ℕ) : ℝ) * (p - 1) ≤ _
  dsimp [Z, T] at hi hct ⊢
  linarith

theorem glyz_ennreal_dyadic_count (d : ℕ) (p : ℝ) :
    ((2 ^ d : ℕ) : ℝ≥0∞) ^ p =
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) * p)) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.rpow_natCast_mul,
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The dyadic bound for a nonnegative exponent holds throughout the
actual frequency shell without changing its constant. -/
theorem glyz_variable_shell_nonneg_power (N : ℕ) {Λ a : ℝ}
    (hΛ : (2 : ℝ) ^ N ≤ Λ) (ha : 0 ≤ a) :
    (2 : ℝ) ^ (a * N) ≤ Λ ^ a := by
  rw [mul_comm a, Real.rpow_natCast_mul (by norm_num)]
  exact Real.rpow_le_rpow (by positivity) hΛ ha

/-- A negative dyadic power differs from the corresponding actual
frequency power by only the fixed factor 2^Q. -/
theorem glyz_variable_shell_decay (N : ℕ) {Λ Q : ℝ}
    (hΛ : 0 < Λ) (hΛ' : Λ ≤ (2 : ℝ) ^ (N + 1)) (hQ : 0 ≤ Q) :
    (2 : ℝ) ^ (-Q * N) ≤ (2 : ℝ) ^ Q * Λ ^ (-Q) := by
  have h := Real.rpow_le_rpow_of_nonpos hΛ hΛ' (neg_nonpos.mpr hQ)
  calc
    _ = (2 : ℝ) ^ Q * ((2 : ℝ) ^ (N + 1)) ^ (-Q) := by
      rw [← Real.rpow_natCast_mul (by norm_num),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- The Fourier error is raised to the actual Lp exponent only after
choosing a sufficiently high integer differentiation order. -/
theorem exists_glyz_variable_tail_power_order (a : ℕ) {ζ p : ℝ}
    (hζ : 0 < ζ) (hp : 0 < p) (B Q : ℝ) :
    ∃ M : ℕ, ∀ N : ℕ, ∀ α : ℝ, |α| ≤ (2 : ℝ) ^ (N + 1) →
      (2 : ℝ) ^ (B * N) *
        ((1 + |α|) ^ a * ((2 : ℝ) ^ (ζ * N)) ^ (-(M : ℝ))) ^ p ≤
      (2 : ℝ) ^ ((2 * a : ℕ) * p) * (2 : ℝ) ^ (-Q * N) := by
  obtain ⟨M, hM⟩ := exists_glyz_variable_tail_order a hζ (B / p) (Q / p)
  refine ⟨M, fun N α hα => ?_⟩
  have h := Real.rpow_le_rpow (by positivity) (hM N α hα) hp.le
  have hleft : ((2 : ℝ) ^ (B / p * N) * (1 + |α|) ^ a *
      ((2 : ℝ) ^ (ζ * N)) ^ (-(M : ℝ))) ^ p =
      (2 : ℝ) ^ (B * N) *
        ((1 + |α|) ^ a * ((2 : ℝ) ^ (ζ * N)) ^ (-(M : ℝ))) ^ p := by
    rw [mul_assoc, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    field_simp
  have hright : ((2 : ℝ) ^ (2 * a) * (2 : ℝ) ^ (-(Q / p) * N)) ^ p =
      (2 : ℝ) ^ ((2 * a : ℕ) * p) * (2 : ℝ) ^ (-Q * N) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    field_simp
  simpa only [hleft, hright] using h

end PlanarNikodym
