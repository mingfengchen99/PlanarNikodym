import PlanarNikodym.Analysis.Fourier.GlyzVariableSpectralBudget

/-! The actual variable-scale schedule retains a fixed offset in its
Fourier margin. The layer count is independent even of that offset;
only the harmless counting constant changes. -/
noncomputable section
namespace PlanarNikodym

/-- One layer count works for all frequency-independent offsets. -/
theorem exists_glyz_variable_offset_layers (n : ℕ) (hn : 0 < n) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ M : ℕ, ∀ N c T : ℕ, T ≤ N →
      glyzVariableStoppedDepth n (⌈ζ * N⌉₊ + c)
        (2 * (⌈ζ * N⌉₊ + c) + 2 * n) T M = T := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (1 / ζ)
    (by linarith [one_div_pos.mpr hnR] : 1 < 1 + 1 / (n : ℝ))
  refine ⟨M, fun N c T hTN => ?_⟩
  let Z := ⌈ζ * N⌉₊ + c
  have hZN : ζ * N ≤ (Z : ℝ) := by
    have h := Nat.le_ceil (ζ * (N : ℝ))
    dsimp [Z]
    push_cast
    linarith
  have hg := glyzVariableDepth_growth n Z (2 * Z + 2 * n) M hn (by omega)
  have hZ0 : 0 ≤ (Z : ℝ) := Nat.cast_nonneg _
  have hpow0 : 0 ≤ (1 + 1 / (n : ℝ)) ^ M := by positivity
  have hMζ : 1 ≤ (1 + 1 / (n : ℝ)) ^ M * ζ := (div_le_iff₀ hζ).mp hM.le
  have hmult := mul_le_mul_of_nonneg_left hZN hpow0
  have hNmul := mul_le_mul_of_nonneg_right hMζ (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hN : (N : ℝ) ≤ glyzVariableDepth n Z (2 * Z + 2 * n) M := by
    push_cast at hg
    nlinarith
  unfold glyzVariableStoppedDepth
  apply min_eq_left
  exact hTN.trans (by exact_mod_cast hN)

/-- A nontrivial stopped step automatically lies below the spectral
terminal scale, including the case of frequencies below the fixed offset. -/
theorem glyz_variable_offset_step_budgets (n N Z j : ℕ)
    (hstep : glyzVariableStoppedDepth n Z (2 * Z + 2 * n)
        (glyzVariableTerminalDepth n N Z) j <
      glyzVariableStoppedDepth n Z (2 * Z + 2 * n)
        (glyzVariableTerminalDepth n N Z) (j + 1)) :
    let d := glyzVariableStoppedDepth n Z (2 * Z + 2 * n)
      (glyzVariableTerminalDepth n N Z) j
    let d' := glyzVariableStoppedDepth n Z (2 * Z + 2 * n)
      (glyzVariableTerminalDepth n N Z) (j + 1)
    n * (d' - d) + Z ≤ d ∧ n * d' + Z ≤ N := by
  dsimp
  constructor
  · exact glyzVariableStoppedDepth_step_budget n Z (2 * Z + 2 * n)
      (glyzVariableTerminalDepth n N Z) j (by omega) hstep
  · have hZN : Z ≤ N := by
      by_contra hh
      have he : glyzVariableTerminalDepth n N Z = 0 := by
        simp [glyzVariableTerminalDepth, Nat.sub_eq_zero_of_le (by omega : N ≤ Z)]
      simp only [he, glyzVariableStoppedDepth, Nat.zero_min] at hstep
      omega
    have hb := glyzVariableTerminalDepth_spectral_budget n N Z hZN
    have hc : glyzVariableStoppedDepth n Z (2 * Z + 2 * n)
        (glyzVariableTerminalDepth n N Z) (j + 1) ≤ glyzVariableTerminalDepth n N Z :=
      min_le_left _ _
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left n hc) Z).trans hb

/-- Both rounding and the fixed Fourier offset only affect the constant
in the initial/final counting cost. -/
theorem exists_glyz_variable_offset_counting_budget (n : ℕ) (hn : 0 < n)
    {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ N c : ℕ,
      ((2 * (⌈ζ * N⌉₊ + c) + 2 * n : ℕ) : ℝ) * (p - 1) +
        ((glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N (⌈ζ * N⌉₊ + c) : ℕ) : ℝ) *
          (p - 1) ≤ ε * N + (2 * n + 3 * c + 5) * (p - 1) := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let ζ := ε / (4 * p)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hζ : 0 < ζ := div_pos hε (by positivity)
  refine ⟨ζ, hζ, fun N c => ?_⟩
  have hi := glyzVariableDepth_initial_budget n N hζ.le
  have hg := glyzVariableTerminalDepth_gap n N (⌈ζ * N⌉₊ + c) hn
  have hgR : (n : ℝ) *
      ((glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N (⌈ζ * N⌉₊ + c) : ℕ) : ℝ) ≤
      (⌈ζ * N⌉₊ : ℝ) + c + 2 * n := by exact_mod_cast hg
  have hc := Nat.ceil_lt_add_one (show 0 ≤ ζ * (N : ℝ) by positivity)
  have hgap : ((glyzVariableFinalDepth n N -
      glyzVariableTerminalDepth n N (⌈ζ * N⌉₊ + c) : ℕ) : ℝ) ≤ ζ * N + c + 3 := by
    have hnon := mul_nonneg (sub_nonneg.mpr hnR)
      (show 0 ≤ ζ * (N : ℝ) + c + 1 by positivity)
    nlinarith
  have hcost : 3 * ζ * (p - 1) ≤ ε := by
    have heq : ζ * (4 * p) = ε := div_mul_cancel₀ ε (by positivity : 4 * p ≠ 0)
    nlinarith
  have hi' := mul_le_mul_of_nonneg_right hi (sub_nonneg.mpr hp)
  have hg' := mul_le_mul_of_nonneg_right hgap (sub_nonneg.mpr hp)
  have hc' := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  push_cast at hi' ⊢
  nlinarith

end PlanarNikodym
