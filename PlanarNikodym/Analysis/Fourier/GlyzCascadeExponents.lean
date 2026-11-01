import PlanarNikodym.Analysis.Fourier.GlyzFinalFrequencyScale
import PlanarNikodym.Analysis.Fourier.GlyzCriticalMomentDecoupling

/-! Exact exponents and rounded depths for the successive degree
reductions. The last degree is two and the final width is r^(-1/2). -/
noncomputable section
namespace PlanarNikodym

def glyzCascadeExponent (D j : ℕ) (p : ℝ) : ℝ :=
  (p - 1) / j - D + ((j : ℝ) - 1) / 2

theorem glyzCascadeExponent_top (D : ℕ) (hD : 0 < D) (p : ℝ) :
    glyzCascadeExponent D D p = (p - glyzCriticalExponent D / 2 - 1) / D := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  dsimp [glyzCascadeExponent, glyzCriticalExponent]
  field_simp
  ring

theorem glyzCascadeExponent_step (D j : ℕ) (hj : 0 < j) (p : ℝ) :
    glyzCascadeExponent D (j + 1) p +
      (p - glyzCriticalExponent j / 2 - 1) * (1 / (j : ℝ) - 1 / (j + 1 : ℕ)) =
      glyzCascadeExponent D j p := by
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hj1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp [glyzCascadeExponent, glyzCriticalExponent]
  push_cast
  field_simp
  ring

theorem glyzCascadeExponent_two (D : ℕ) (p : ℝ) :
    glyzCascadeExponent D 2 p = p / 2 - D := by
  dsimp [glyzCascadeExponent]
  norm_num
  ring

theorem glyzVariableFinalDepth_le (k N : ℕ) (hk : 0 < k) :
    glyzVariableFinalDepth k N ≤ N := by
  obtain ⟨hl, hu⟩ := glyzVariableFinalDepth_integer_bounds hk N
  by_contra h
  have hsucc : N + 1 ≤ glyzVariableFinalDepth k N := by omega
  have hprod := Nat.mul_le_mul_left k hsucc
  nlinarith

theorem glyzVariableFinalDepth_antitone {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) (N : ℕ) :
    glyzVariableFinalDepth l N ≤ glyzVariableFinalDepth k N := by
  have hl : 0 < l := hk.trans_le hkl
  obtain ⟨hlo, hhi⟩ := glyzVariableFinalDepth_integer_bounds hk N
  obtain ⟨hlo', hhi'⟩ := glyzVariableFinalDepth_integer_bounds hl N
  by_contra h
  have hplus : glyzVariableFinalDepth k N + 1 ≤ glyzVariableFinalDepth l N := by omega
  have hprod := Nat.mul_le_mul_left l hplus
  have hcomp := Nat.mul_le_mul_right (glyzVariableFinalDepth k N) hkl
  nlinarith

/-- Rounding and a fixed coarsening cost only a fixed additive depth. -/
theorem glyz_cascade_depth_gap (k N s : ℕ) (hk : 0 < k) :
    (((glyzVariableFinalDepth k N - s) -
      (glyzVariableFinalDepth (k + 1) N - s) : ℕ) : ℝ) ≤
      (1 / (k : ℝ) - 1 / (k + 1 : ℕ)) * N + (s + 1) := by
  have hmono := glyzVariableFinalDepth_antitone hk (Nat.le_succ k) N
  have hsub : glyzVariableFinalDepth (k + 1) N - s ≤ glyzVariableFinalDepth k N - s :=
    Nat.sub_le_sub_right hmono s
  have hs : (glyzVariableFinalDepth (k + 1) N : ℝ) - s ≤
      ((glyzVariableFinalDepth (k + 1) N - s : ℕ) : ℝ) := by
    have hn : glyzVariableFinalDepth (k + 1) N ≤
        glyzVariableFinalDepth (k + 1) N - s + s := by omega
    have hr : (glyzVariableFinalDepth (k + 1) N : ℝ) ≤
        ((glyzVariableFinalDepth (k + 1) N - s : ℕ) : ℝ) + s := by exact_mod_cast hn
    linarith
  obtain ⟨_, hu⟩ := glyzVariableFinalDepth_real_bounds hk N
  obtain ⟨hl, _⟩ := glyzVariableFinalDepth_real_bounds (Nat.succ_pos k) N
  rw [Nat.cast_sub hsub]
  have hf : ((glyzVariableFinalDepth k N - s : ℕ) : ℝ) ≤
      (glyzVariableFinalDepth k N : ℝ) := by exact_mod_cast Nat.sub_le (glyzVariableFinalDepth k N) s
  have he : (1 / (k : ℝ) - 1 / (k + 1 : ℕ)) * N =
      (N : ℝ) / k - (N : ℝ) / (k + 1 : ℕ) := by ring
  rw [he]
  linarith

end PlanarNikodym
