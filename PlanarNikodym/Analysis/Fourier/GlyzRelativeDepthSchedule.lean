import PlanarNikodym.Analysis.Fourier.GlyzVariableNumericalBudget

/-! Relative schedules start with an already decoupled dyadic family.
The degree may decrease without paying again for its existing depth. -/
noncomputable section
namespace PlanarNikodym

/-- The usual finite schedule, started no earlier than a prescribed depth. -/
def glyzRelativeDepth (k N Z A : ℕ) (j : ℕ) : ℕ :=
  max A (glyzVariableStoppedDepth k Z (2 * Z + 2 * k)
    (glyzVariableTerminalDepth k N Z) j)

theorem glyzRelativeDepth_mono (k N Z A j : ℕ) :
    glyzRelativeDepth k N Z A j ≤ glyzRelativeDepth k N Z A (j + 1) :=
  max_le_max_left _ (glyzVariableStoppedDepth_mono _ _ _ _ _)

theorem glyzRelativeDepth_step_budgets (k N Z A j : ℕ)
    (h : glyzRelativeDepth k N Z A j < glyzRelativeDepth k N Z A (j + 1)) :
    k * (glyzRelativeDepth k N Z A (j + 1) - glyzRelativeDepth k N Z A j) + Z ≤
        glyzRelativeDepth k N Z A j ∧
      k * glyzRelativeDepth k N Z A (j + 1) + Z ≤ N := by
  let u := glyzVariableStoppedDepth k Z (2 * Z + 2 * k)
    (glyzVariableTerminalDepth k N Z)
  have hnext : glyzRelativeDepth k N Z A (j + 1) = u (j + 1) := by
    dsimp [glyzRelativeDepth, u] at *
    omega
  have hstrict : u j < u (j + 1) := by
    dsimp [glyzRelativeDepth, u] at *
    omega
  have hbud := glyz_variable_offset_step_budgets k N Z j hstrict
  have hu : u j ≤ glyzRelativeDepth k N Z A j := le_max_right _ _
  rw [hnext]
  exact ⟨(Nat.add_le_add_right (Nat.mul_le_mul_left k
    (Nat.sub_le_sub_left hu _)) Z).trans (hbud.1.trans hu), hbud.2⟩

/-- Initial and final counting cost only epsilon times the original
frequency, while the main exponent counts only genuinely new depths. -/
theorem exists_glyz_relative_exponent_budget (k : ℕ) (hk : 0 < k)
    {p σ ε : ℝ} (hp : 1 ≤ p) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ ζ η : ℝ, 0 < ζ ∧ 0 < η ∧ ∀ N c A F : ℕ,
      A ≤ F → glyzVariableTerminalDepth k N (⌈ζ * N⌉₊ + c) ≤ F →
      F ≤ glyzVariableFinalDepth k N →
      let Z := ⌈ζ * N⌉₊ + c
      let T := glyzVariableTerminalDepth k N Z
      let a := max A (min T (2 * Z + 2 * k))
      let b := max A T
      ((a - A : ℕ) : ℝ) * (p - 1) + (σ + η) * ((b - a : ℕ) : ℝ) +
        ((F - b : ℕ) : ℝ) * (p - 1) ≤
      σ * ((F - A : ℕ) : ℝ) + ε * N + (2 * k + 3 * c + 5) * (p - 1) := by
  obtain ⟨ζ, hζ, hcount⟩ :=
    exists_glyz_variable_offset_counting_budget k hk hp (half_pos hε)
  refine ⟨ζ, ε / 2, hζ, half_pos hε, fun N c A F hAF hTF hFF => ?_⟩
  let Z := ⌈ζ * N⌉₊ + c
  let T := glyzVariableTerminalDepth k N Z
  let a := max A (min T (2 * Z + 2 * k))
  let b := max A T
  have haA : A ≤ a := le_max_left _ _
  have hab : a ≤ b := max_le_max_left _ (min_le_left _ _)
  have hbF : b ≤ F := max_le hAF hTF
  have hi : a - A ≤ 2 * Z + 2 * k := by dsimp [a]; omega
  have hf : F - b ≤ glyzVariableFinalDepth k N - T := by
    dsimp [b]; omega
  have hba : b - a ≤ F - A := by omega
  have hbT : b - a ≤ T := by dsimp [b, a]; omega
  have hTN : T ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hbaN : ((b - a : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hbT.trans hTN
  have h1 := mul_le_mul_of_nonneg_right
    (show ((a - A : ℕ) : ℝ) ≤ (2 * Z + 2 * k : ℕ) by exact_mod_cast hi)
    (sub_nonneg.mpr hp)
  have h2 := mul_le_mul_of_nonneg_right
    (show ((F - b : ℕ) : ℝ) ≤ (glyzVariableFinalDepth k N - T : ℕ) by exact_mod_cast hf)
    (sub_nonneg.mpr hp)
  have h3 := mul_le_mul_of_nonneg_left
    (show ((b - a : ℕ) : ℝ) ≤ (F - A : ℕ) by exact_mod_cast hba) hσ
  have h4 := mul_le_mul_of_nonneg_left hbaN (half_pos hε).le
  have hc := hcount N c
  change ((a - A : ℕ) : ℝ) * (p - 1) + (σ + ε / 2) * ((b - a : ℕ) : ℝ) +
      ((F - b : ℕ) : ℝ) * (p - 1) ≤ _
  dsimp [Z, T] at h1 h2
  nlinarith

end PlanarNikodym
