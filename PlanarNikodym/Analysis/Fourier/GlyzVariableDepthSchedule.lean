import PlanarNikodym.Analysis.Fourier.GlyzFixedStepSchedule

/-! Integer schedules for variable-coefficient Taylor localization.
The frequency-tail margin Z is retained at every step; floor errors are
absorbed by a fixed shift of n in the geometric growth estimate. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

def glyzVariableDepth (n Z d₀ : ℕ) : ℕ → ℕ
  | 0 => d₀
  | j + 1 => glyzVariableDepth n Z d₀ j + (glyzVariableDepth n Z d₀ j - Z) / n

theorem glyzVariableDepth_mono (n Z d₀ j : ℕ) :
    glyzVariableDepth n Z d₀ j ≤ glyzVariableDepth n Z d₀ (j + 1) := by
  exact Nat.le_add_right _ _

theorem glyzVariableDepth_ge (n Z d₀ j : ℕ) : d₀ ≤ glyzVariableDepth n Z d₀ j := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih.trans (glyzVariableDepth_mono n Z d₀ j)

/-- Exact integer support budget: n times the relative child depth
plus the Fourier-tail margin does not exceed the parent depth. -/
theorem glyzVariableDepth_step_budget (n Z d₀ j : ℕ) (hZ : Z ≤ d₀) :
    n * (glyzVariableDepth n Z d₀ (j + 1) - glyzVariableDepth n Z d₀ j) + Z ≤
      glyzVariableDepth n Z d₀ j := by
  have h := Nat.mul_div_le (glyzVariableDepth n Z d₀ j - Z) n
  have hz := hZ.trans (glyzVariableDepth_ge n Z d₀ j)
  simp only [glyzVariableDepth, Nat.add_sub_cancel_left]
  omega

/-- Uniform lower growth, including the loss from integer division. -/
theorem glyzVariableDepth_growth (n Z d₀ j : ℕ) (hn : 0 < n) (hbase : Z + n ≤ d₀) :
    (Z + n : ℝ) + (1 + 1 / (n : ℝ)) ^ j * ((d₀ : ℝ) - (Z + n)) ≤
      glyzVariableDepth n Z d₀ j := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  induction j with
  | zero => simp [glyzVariableDepth]
  | succ j ih =>
    let d := glyzVariableDepth n Z d₀ j
    have hdZ : Z ≤ d := (by omega : Z ≤ d₀).trans (glyzVariableDepth_ge n Z d₀ j)
    have hdiv := Nat.div_add_mod (d - Z) n
    have hmod := Nat.mod_lt (d - Z) hn
    have hsub : ((d - Z : ℕ) : ℝ) = (d : ℝ) - Z := Nat.cast_sub hdZ
    have he : (n : ℝ) * ((d - Z) / n : ℕ) + ((d - Z) % n : ℕ) = (d : ℝ) - Z := by
      rw [← hsub]
      exact_mod_cast hdiv
    have hm : (((d - Z) % n : ℕ) : ℝ) < n := by exact_mod_cast hmod
    have hfloor : (d : ℝ) - Z - n ≤ (n : ℝ) * ((d - Z) / n : ℕ) := by linarith
    have hstep : (1 + 1 / (n : ℝ)) * ((d : ℝ) - (Z + n)) + (Z + n) ≤
        (d : ℝ) + ((d - Z) / n : ℕ) := by
      apply (mul_le_mul_iff_right₀ hnR).mp
      field_simp
      nlinarith
    have hmulp := mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ 1 + 1 / (n : ℝ))
    rw [pow_succ]
    change _ ≤ ((d + (d - Z) / n : ℕ) : ℝ)
    push_cast
    nlinarith

def glyzVariableStoppedDepth (n Z d₀ T j : ℕ) := min T (glyzVariableDepth n Z d₀ j)

theorem glyzVariableStoppedDepth_mono (n Z d₀ T j : ℕ) :
    glyzVariableStoppedDepth n Z d₀ T j ≤ glyzVariableStoppedDepth n Z d₀ T (j + 1) :=
  min_le_min_left T (glyzVariableDepth_mono n Z d₀ j)

theorem glyzVariableStoppedDepth_step_budget (n Z d₀ T j : ℕ) (hZ : Z ≤ d₀)
    (hstep : glyzVariableStoppedDepth n Z d₀ T j < glyzVariableStoppedDepth n Z d₀ T (j + 1)) :
    n * (glyzVariableStoppedDepth n Z d₀ T (j + 1) - glyzVariableStoppedDepth n Z d₀ T j) + Z ≤
      glyzVariableStoppedDepth n Z d₀ T j := by
  have hbudget := glyzVariableDepth_step_budget n Z d₀ j hZ
  have hd : glyzVariableDepth n Z d₀ j < T := by
    unfold glyzVariableStoppedDepth at hstep
    omega
  unfold glyzVariableStoppedDepth
  rw [min_eq_right hd.le]
  apply le_trans _ hbudget
  gcongr
  exact min_le_right _ _

/-- A number of layers depending only on n and ζ reaches every target
T≤N. It is chosen before the frequency N, including all small N. -/
theorem exists_glyz_variable_depth_layers (n : ℕ) (hn : 0 < n) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ M : ℕ, ∀ N T : ℕ, T ≤ N →
      glyzVariableStoppedDepth n ⌈ζ * N⌉₊ (2 * ⌈ζ * N⌉₊ + 2 * n) T M = T := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (1 / ζ) (by linarith [one_div_pos.mpr hnR] : 1 < 1 + 1 / (n : ℝ))
  refine ⟨M, fun N T hTN => ?_⟩
  let Z := ⌈ζ * N⌉₊
  have hZN : ζ * N ≤ (Z : ℝ) := Nat.le_ceil _
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

/-- The initial trivial subdivision costs only 2ζN plus a fixed
integer amount. -/
theorem glyzVariableDepth_initial_budget (n N : ℕ) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ((2 * ⌈ζ * N⌉₊ + 2 * n : ℕ) : ℝ) ≤ 2 * ζ * N + (2 * n + 2) := by
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ ζ * (N : ℝ) by positivity)
  push_cast
  linarith

/-- The total relative depth is exactly the finest minus the initial
depth, so all scale powers telescope without accumulating losses. -/
theorem glyzVariableStoppedDepth_telescope (n Z d₀ T M : ℕ) :
    (∑ j ∈ Finset.range M, (glyzVariableStoppedDepth n Z d₀ T (j + 1) -
      glyzVariableStoppedDepth n Z d₀ T j)) + glyzVariableStoppedDepth n Z d₀ T 0 =
        glyzVariableStoppedDepth n Z d₀ T M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hm := glyzVariableStoppedDepth_mono n Z d₀ T M
    omega

/-- The final target rounds N/n upward; the terminal spectral estimate
rounds (N-Z)/n downward. -/
def glyzVariableFinalDepth (n N : ℕ) := (N + n - 1) / n

def glyzVariableTerminalDepth (n N Z : ℕ) := (N - Z) / n

theorem glyzVariableTerminalDepth_le_final (n N Z : ℕ) (hn : 0 < n) :
    glyzVariableTerminalDepth n N Z ≤ glyzVariableFinalDepth n N := by
  unfold glyzVariableTerminalDepth glyzVariableFinalDepth
  exact Nat.div_le_div_right (by omega)

/-- The last trivial subdivision loses at most Z/n plus two fixed
dyadic generations. -/
theorem glyzVariableTerminalDepth_gap (n N Z : ℕ) (hn : 0 < n) :
    n * (glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N Z) ≤ Z + 2 * n := by
  have hle := glyzVariableTerminalDepth_le_final n N Z hn
  have hf := Nat.mul_div_le (N + n - 1) n
  have ht := Nat.div_add_mod (N - Z) n
  have hmod := Nat.mod_lt (N - Z) hn
  have hd : glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N Z +
      glyzVariableTerminalDepth n N Z = glyzVariableFinalDepth n N := Nat.sub_add_cancel hle
  have hmul := congrArg (fun x : ℕ => n * x) hd
  simp only [Nat.mul_add] at hmul
  unfold glyzVariableFinalDepth glyzVariableTerminalDepth at hmul ⊢
  omega

theorem glyzVariableTerminalDepth_spectral_budget (n N Z : ℕ) (hZN : Z ≤ N) :
    n * glyzVariableTerminalDepth n N Z + Z ≤ N := by
  have h := Nat.mul_div_le (N - Z) n
  unfold glyzVariableTerminalDepth
  omega

/-- Initial and terminal counting losses use an arbitrarily small
part of the desired exponent. The harmless integer terms remain as a
single fixed multiplicative constant. -/
theorem exists_glyz_variable_counting_budget (n : ℕ) (hn : 0 < n)
    {p ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ N : ℕ,
      ((2 * ⌈ζ * N⌉₊ + 2 * n : ℕ) : ℝ) * (p - 1) +
        ((glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N ⌈ζ * N⌉₊ : ℕ) : ℝ) *
          (p - 1) ≤ ε * N + (2 * n + 5) * (p - 1) := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let ζ := ε / (4 * p)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hζ : 0 < ζ := div_pos hε (by positivity)
  refine ⟨ζ, hζ, fun N => ?_⟩
  have hi := glyzVariableDepth_initial_budget n N hζ.le
  have hg := glyzVariableTerminalDepth_gap n N ⌈ζ * N⌉₊ hn
  have hgR : (n : ℝ) *
      ((glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N ⌈ζ * N⌉₊ : ℕ) : ℝ) ≤
      (⌈ζ * N⌉₊ : ℝ) + 2 * n := by exact_mod_cast hg
  have hc := Nat.ceil_lt_add_one (show 0 ≤ ζ * (N : ℝ) by positivity)
  have hgap0 : (0 : ℝ) ≤
      ((glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N ⌈ζ * N⌉₊ : ℕ) : ℝ) := by positivity
  have hgap : ((glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N ⌈ζ * N⌉₊ : ℕ) : ℝ) ≤
      ζ * N + 3 := by
    have hn0 : 0 < (n : ℝ) := by positivity
    have hmul : (n : ℝ) *
        (((glyzVariableFinalDepth n N - glyzVariableTerminalDepth n N ⌈ζ * N⌉₊ : ℕ) : ℝ) - 2) ≤
        (⌈ζ * N⌉₊ : ℝ) := by linarith
    have hnon := mul_nonneg (sub_nonneg.mpr hnR)
      (show 0 ≤ ζ * (N : ℝ) + 1 by positivity)
    nlinarith
  have hcost : 3 * ζ * (p - 1) ≤ ε := by
    have heq : ζ * (4 * p) = ε := div_mul_cancel₀ ε (by positivity : 4 * p ≠ 0)
    nlinarith
  have hi' := mul_le_mul_of_nonneg_right hi (sub_nonneg.mpr hp)
  have hg' := mul_le_mul_of_nonneg_right hgap (sub_nonneg.mpr hp)
  have hc' := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

end PlanarNikodym
