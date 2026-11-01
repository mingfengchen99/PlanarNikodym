import PlanarNikodym.Analysis.Fourier.GlyzVariableScheduledIteration
import PlanarNikodym.Analysis.Fourier.GlyzFinalFrequencyScale

/-! The actual stopped iteration can finish at any depth above its
analytic terminal depth. A fixed larger Fourier offset permits a fixed
number of generations of coarsening of the usual final scale. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_actual_kernel_stopped_iteration_to {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (k N Z M F : ℕ) (hTF : glyzVariableTerminalDepth k N Z ≤ F)
    (hM : glyzVariableStoppedDepth k Z (2 * Z + 2 * k)
      (glyzVariableTerminalDepth k N Z) M = glyzVariableTerminalDepth k N Z)
    {p : ℝ} (hp : 1 ≤ p)
    (C b e : ℝ≥0∞) (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hstep : ∀ d m : ℕ, d < m → k * (m - d) + Z ≤ d → k * m + Z ≤ N →
      ∀ i < 2 ^ d,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g d i x‖ₑ ^ p ∂μ) ≤
        (C * b ^ (m - d)) * glyzDyadicBlock
          (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) m d i +
        e * (∫⁻ y, ‖glyzDyadicInput d i g y‖ₑ) ^ p) :
    let T := glyzVariableTerminalDepth k N Z
    let d := min T (2 * Z + 2 * k)
    (∫⁻ x, ‖∫ y, g y * H (x, y)‖ₑ ^ p ∂μ) ≤
      ((2 ^ d : ℕ) : ℝ≥0∞) ^ (p - 1) * (C ^ M * b ^ (T - d)) *
        ((2 ^ (F - T) : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g F p +
      ((2 ^ d : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ((M : ℝ≥0∞) * (C ^ M * b ^ (T - d)) * e) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
  let T := glyzVariableTerminalDepth k N Z
  let n := glyzVariableStoppedDepth k Z (2 * Z + 2 * k) T
  have hnM : n M = T := hM
  have hmono : ∀ j < M, n j ≤ n (j + 1) :=
    fun j _ => glyzVariableStoppedDepth_mono k Z (2 * Z + 2 * k) T j
  have hh := glyz_actual_kernel_uniform_iteration μ hH hc hg hs M F n
    (by rw [hnM]; exact hTF) hp C b e hC hb hmono
  have hsteps : ∀ j < M, ∀ i < 2 ^ n j,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g (n j) i x‖ₑ ^ p ∂μ) ≤
        (C * b ^ (n (j + 1) - n j)) * glyzDyadicBlock
          (fun a => ∫⁻ x, ‖glyzDyadicKernelPiece H g (n (j + 1)) a x‖ₑ ^ p ∂μ)
          (n (j + 1)) (n j) i +
        e * (∫⁻ y, ‖glyzDyadicInput (n j) i g y‖ₑ) ^ p := by
    intro j hj i hi
    by_cases heq : n j = n (j + 1)
    · rw [← heq]
      simp only [Nat.sub_self, pow_zero, mul_one, glyzDyadicBlock_finest]
      exact le_add_of_le_left (le_mul_of_one_le_left' hC)
    · have hlt : n j < n (j + 1) := lt_of_le_of_ne (hmono j hj) heq
      have hbud := glyz_variable_offset_step_budgets k N Z j hlt
      exact hstep (n j) (n (j + 1)) hlt hbud.1 hbud.2 i hi
  have h := hh hsteps
  simpa only [hnM, n, glyzVariableStoppedDepth, glyzVariableDepth, T] using h

theorem glyz_variable_terminal_le_coarse (k N Z s : ℕ) (hk : 0 < k)
    (hZ : k * s ≤ Z) :
    glyzVariableTerminalDepth k N Z ≤ glyzVariableFinalDepth k N - s := by
  let T := glyzVariableTerminalDepth k N Z
  let F := glyzVariableFinalDepth k N
  by_cases hT : T = 0
  · change T ≤ _
    rw [hT]
    exact Nat.zero_le _
  have hZN : Z ≤ N := by
    by_contra h
    have he : T = 0 := by
      dsimp only [T, glyzVariableTerminalDepth]
      rw [Nat.sub_eq_zero_of_le (by omega : N ≤ Z), Nat.zero_div]
    exact hT he
  have hterminal := glyzVariableTerminalDepth_spectral_budget k N Z hZN
  have hfinal := (glyzVariableFinalDepth_integer_bounds hk N).1
  have hmul : k * (T + s) ≤ k * F := by
    dsimp only [T, F]
    nlinarith
  have hsum : T + s ≤ F := le_of_mul_le_mul_left hmul hk
  change T ≤ F - s
  omega

end PlanarNikodym
