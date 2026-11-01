import PlanarNikodym.Analysis.Fourier.GlyzVariableKernelIteration
import PlanarNikodym.Analysis.Fourier.GlyzVariableNumericalBudget

/-! The integer variable-scale schedule applied to one actual kernel.
Only strict refinements use the analytic parent estimate. Repeated
terminal scales are handled by the exact singleton-block identity. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_actual_kernel_stopped_iteration {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (k N Z M : ℕ) (hk : 0 < k)
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
    let F := glyzVariableFinalDepth k N
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
  have hh := glyz_actual_kernel_uniform_iteration μ hH hc hg hs M
    (glyzVariableFinalDepth k N) n
    (by rw [hnM]; exact glyzVariableTerminalDepth_le_final k N Z hk)
    hp C b e hC hb hmono
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

/-- Exact conversion of all finite-scale factors into a single real
power. The layer constant appears only to the fixed integer power M. -/
theorem glyz_variable_iteration_coefficient (d T F M : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (p a : ℝ) :
    ((2 ^ d : ℕ) : ℝ≥0∞) ^ (p - 1) *
      ((ENNReal.ofReal C) ^ M * (ENNReal.ofReal ((2 : ℝ) ^ a)) ^ (T - d)) *
      ((2 ^ (F - T) : ℕ) : ℝ≥0∞) ^ (p - 1) =
    ENNReal.ofReal (C ^ M *
      (2 : ℝ) ^ ((d : ℝ) * (p - 1) + a * ((T - d : ℕ) : ℝ) +
        ((F - T : ℕ) : ℝ) * (p - 1))) := by
  rw [glyz_ennreal_dyadic_count, glyz_ennreal_dyadic_count,
    ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_pow (by positivity),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_mul (pow_nonneg hC _),
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  ring

end PlanarNikodym
