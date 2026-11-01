import PlanarNikodym.Analysis.Fourier.GlyzRelativeDepthSchedule
import PlanarNikodym.Analysis.Fourier.GlyzVariableScheduledIteration

/-! Actual dyadic energy iteration starting at an existing scale. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_actual_kernel_relative_uniform_iteration {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (M A F : ℕ) (n : ℕ → ℕ) (hAn : A ≤ n 0) (hnF : n M ≤ F)
    {p : ℝ} (hp : 1 ≤ p) (C b e : ℝ≥0∞) (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hmono : ∀ j < M, n j ≤ n (j + 1))
    (hstep : ∀ j < M, ∀ i < 2 ^ n j,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g (n j) i x‖ₑ ^ p ∂μ) ≤
        (C * b ^ (n (j + 1) - n j)) * glyzDyadicBlock
          (fun k => ∫⁻ x, ‖glyzDyadicKernelPiece H g (n (j + 1)) k x‖ₑ ^ p ∂μ)
          (n (j + 1)) (n j) i + e * (∫⁻ y, ‖glyzDyadicInput (n j) i g y‖ₑ) ^ p) :
    glyzDyadicKernelEnergy μ H g A p ≤
      ((2 ^ (n 0 - A) : ℕ) : ℝ≥0∞) ^ (p - 1) * (C ^ M * b ^ (n M - n 0)) *
        ((2 ^ (F - n M) : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g F p +
      ((2 ^ (n 0 - A) : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ((M : ℝ≥0∞) * (C ^ M * b ^ (n M - n 0)) * e) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
  let D := fun j => C * b ^ (n (j + 1) - n j)
  have hi := glyzDyadicKernelEnergy_trivial_refine μ hH hc hg hs A (n 0) hAn hp
  have hit := glyzDyadicKernelEnergy_iterate μ H hg hs M n hp D (fun _ => e) hmono hstep
  have ht := glyzDyadicKernelEnergy_trivial_refine μ hH hc hg hs (n M) F hnF hp
  have hprod : (∏ j ∈ Finset.range M, D j) = C ^ M * b ^ (n M - n 0) :=
    glyz_depth_coefficient_product C b n M hmono
  have herr : (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, D i) * e) ≤
      (M : ℝ≥0∞) * (C ^ M * b ^ (n M - n 0)) * e := by
    calc
      _ ≤ ∑ _j ∈ Finset.range M, (C ^ M * b ^ (n M - n 0)) * e := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := glyz_depth_prefix_le_final C b hC hb n M j
          (Finset.mem_range.mp hj).le hmono
        simpa [D, mul_comm] using mul_le_mul_right hh e
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  rw [hprod] at hit
  calc
    _ ≤ ((2 ^ (n 0 - A) : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ((C ^ M * b ^ (n M - n 0)) *
          (((2 ^ (F - n M) : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g F p) +
          ((M : ℝ≥0∞) * (C ^ M * b ^ (n M - n 0)) * e) * (∫⁻ y, ‖g y‖ₑ) ^ p) := by
      apply hi.trans
      gcongr
      exact hit.trans (by gcongr)
    _ = _ := by ring

theorem glyz_actual_kernel_relative_stopped_iteration {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (k N Z M A F : ℕ) (hAF : A ≤ F) (hTF : glyzVariableTerminalDepth k N Z ≤ F)
    (hM : glyzVariableStoppedDepth k Z (2 * Z + 2 * k)
      (glyzVariableTerminalDepth k N Z) M = glyzVariableTerminalDepth k N Z)
    {p : ℝ} (hp : 1 ≤ p) (C b e : ℝ≥0∞) (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hstep : ∀ d m : ℕ, d < m → k * (m - d) + Z ≤ d → k * m + Z ≤ N →
      ∀ i < 2 ^ d, (∫⁻ x, ‖glyzDyadicKernelPiece H g d i x‖ₑ ^ p ∂μ) ≤
        (C * b ^ (m - d)) * glyzDyadicBlock
          (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) m d i +
        e * (∫⁻ y, ‖glyzDyadicInput d i g y‖ₑ) ^ p) :
    let T := glyzVariableTerminalDepth k N Z
    let a := max A (min T (2 * Z + 2 * k))
    let b' := max A T
    glyzDyadicKernelEnergy μ H g A p ≤
      ((2 ^ (a - A) : ℕ) : ℝ≥0∞) ^ (p - 1) * (C ^ M * b ^ (b' - a)) *
        ((2 ^ (F - b') : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g F p +
      ((2 ^ (a - A) : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ((M : ℝ≥0∞) * (C ^ M * b ^ (b' - a)) * e) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
  let n := glyzRelativeDepth k N Z A
  have hnM : n M = max A (glyzVariableTerminalDepth k N Z) := by
    simp only [n, glyzRelativeDepth, hM]
  have hmono : ∀ j < M, n j ≤ n (j + 1) :=
    fun j _ => glyzRelativeDepth_mono k N Z A j
  have hh := glyz_actual_kernel_relative_uniform_iteration μ hH hc hg hs M A F n
    (le_max_left _ _) (by rw [hnM]; exact max_le hAF hTF) hp C b e hC hb hmono
  have hsteps : ∀ j < M, ∀ i < 2 ^ n j,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g (n j) i x‖ₑ ^ p ∂μ) ≤
        (C * b ^ (n (j + 1) - n j)) * glyzDyadicBlock
          (fun a => ∫⁻ x, ‖glyzDyadicKernelPiece H g (n (j + 1)) a x‖ₑ ^ p ∂μ)
          (n (j + 1)) (n j) i + e * (∫⁻ y, ‖glyzDyadicInput (n j) i g y‖ₑ) ^ p := by
    intro j hj i hi
    by_cases heq : n j = n (j + 1)
    · rw [← heq]
      simp only [Nat.sub_self, pow_zero, mul_one, glyzDyadicBlock_finest]
      exact le_add_of_le_left (le_mul_of_one_le_left' hC)
    · have hlt : n j < n (j + 1) := lt_of_le_of_ne (hmono j hj) heq
      have hbud := glyzRelativeDepth_step_budgets k N Z A j hlt
      exact hstep (n j) (n (j + 1)) hlt hbud.1 hbud.2 i hi
  have h := hh hsteps
  simpa only [hnM, n, glyzRelativeDepth, glyzVariableStoppedDepth, glyzVariableDepth] using h

end PlanarNikodym
