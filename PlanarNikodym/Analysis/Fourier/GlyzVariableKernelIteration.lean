import PlanarNikodym.Analysis.Fourier.GlyzDyadicKernelIteration
import PlanarNikodym.Analysis.Fourier.GlyzVariableDepthSchedule

/-! Initial counting, actual intermediate estimates, and final counting
for one genuine kernel and one original input. Scale factors telescope;
errors retain their exact prefix products. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_depth_coefficient_product (C b : ℝ≥0∞) (n : ℕ → ℕ) (M : ℕ)
    (hmono : ∀ j < M, n j ≤ n (j + 1)) :
    (∏ j ∈ Finset.range M, C * b ^ (n (j + 1) - n j)) =
      C ^ M * b ^ (n M - n 0) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hm' : ∀ j ≤ M, n 0 ≤ n j := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih => exact (ih (by omega)).trans (hmono j (by omega))
    rw [Finset.prod_range_succ, ih (fun j hj => hmono j (by omega)), pow_succ]
    have hd : n M - n 0 + (n (M + 1) - n M) = n (M + 1) - n 0 := by
      have h0 := hm' M le_rfl
      have h1 := hmono M (by omega)
      omega
    rw [← hd, pow_add]
    ring

/-- Every prefix coefficient is bounded by the final coefficient if
C and b are at least one. -/
theorem glyz_depth_prefix_le_final (C b : ℝ≥0∞) (hC : 1 ≤ C) (hb : 1 ≤ b)
    (n : ℕ → ℕ) (M j : ℕ) (hj : j ≤ M)
    (hmono : ∀ i < M, n i ≤ n (i + 1)) :
    (∏ i ∈ Finset.range j, C * b ^ (n (i + 1) - n i)) ≤
      C ^ M * b ^ (n M - n 0) := by
  rw [glyz_depth_coefficient_product C b n j (fun i hi => hmono i (by omega))]
  have hdepth : n j ≤ n M := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction r with
    | zero => simp
    | succ r ih =>
      exact (ih (by omega) (fun i hi => hmono i (by omega))).trans
        (hmono (j + r) (by omega))
  gcongr

/-- Complete finite iteration for the actual operator, with no hidden
change of input or intermediate family. -/
theorem glyz_actual_kernel_full_iteration {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (M F : ℕ) (n : ℕ → ℕ) (hnF : n M ≤ F) {p : ℝ} (hp : 1 ≤ p)
    (D e : ℕ → ℝ≥0∞) (hmono : ∀ j < M, n j ≤ n (j + 1))
    (hstep : ∀ j < M, ∀ i < 2 ^ n j,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g (n j) i x‖ₑ ^ p ∂μ) ≤
        D j * glyzDyadicBlock
          (fun k => ∫⁻ x, ‖glyzDyadicKernelPiece H g (n (j + 1)) k x‖ₑ ^ p ∂μ)
          (n (j + 1)) (n j) i + e j * (∫⁻ y, ‖glyzDyadicInput (n j) i g y‖ₑ) ^ p) :
    (∫⁻ x, ‖∫ y, g y * H (x, y)‖ₑ ^ p ∂μ) ≤
      ((2 ^ n 0 : ℕ) : ℝ≥0∞) ^ (p - 1) * (∏ j ∈ Finset.range M, D j) *
        ((2 ^ (F - n M) : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g F p +
      ((2 ^ n 0 : ℕ) : ℝ≥0∞) ^ (p - 1) *
        (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, D i) * e j) *
          (∫⁻ y, ‖g y‖ₑ) ^ p := by
  have hinit := glyzDyadicKernelEnergy_initial μ hH hc hg hs (n 0) hp
  have hiter := glyzDyadicKernelEnergy_iterate μ H hg hs M n hp D e hmono hstep
  have hterm := glyzDyadicKernelEnergy_trivial_refine μ hH hc hg hs (n M) F hnF hp
  calc
    _ ≤ ((2 ^ n 0 : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g (n 0) p := hinit
    _ ≤ ((2 ^ n 0 : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ((∏ j ∈ Finset.range M, D j) *
          (((2 ^ (F - n M) : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g F p) +
          (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, D i) * e j) *
            (∫⁻ y, ‖g y‖ₑ) ^ p) := by gcongr; exact hiter.trans (by gcongr)
    _ = _ := by ring

/-- A fixed per-layer constant accumulates only M times, while every
scale factor telescopes. All error terms share the same L¹ mass. -/
theorem glyz_actual_kernel_uniform_iteration {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (M F : ℕ) (n : ℕ → ℕ) (hnF : n M ≤ F) {p : ℝ} (hp : 1 ≤ p)
    (C b e : ℝ≥0∞) (hC : 1 ≤ C) (hb : 1 ≤ b)
    (hmono : ∀ j < M, n j ≤ n (j + 1))
    (hstep : ∀ j < M, ∀ i < 2 ^ n j,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g (n j) i x‖ₑ ^ p ∂μ) ≤
        (C * b ^ (n (j + 1) - n j)) * glyzDyadicBlock
          (fun k => ∫⁻ x, ‖glyzDyadicKernelPiece H g (n (j + 1)) k x‖ₑ ^ p ∂μ)
          (n (j + 1)) (n j) i + e * (∫⁻ y, ‖glyzDyadicInput (n j) i g y‖ₑ) ^ p) :
    (∫⁻ x, ‖∫ y, g y * H (x, y)‖ₑ ^ p ∂μ) ≤
      ((2 ^ n 0 : ℕ) : ℝ≥0∞) ^ (p - 1) * (C ^ M * b ^ (n M - n 0)) *
        ((2 ^ (F - n M) : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g F p +
      ((2 ^ n 0 : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ((M : ℝ≥0∞) * (C ^ M * b ^ (n M - n 0)) * e) * (∫⁻ y, ‖g y‖ₑ) ^ p := by
  let D := fun j => C * b ^ (n (j + 1) - n j)
  have h := glyz_actual_kernel_full_iteration μ hH hc hg hs M F n hnF hp D (fun _ => e)
    hmono hstep
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
  rw [hprod] at h
  exact h.trans (by gcongr)

end PlanarNikodym
