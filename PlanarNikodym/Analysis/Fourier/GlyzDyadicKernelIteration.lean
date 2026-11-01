import PlanarNikodym.Analysis.Fourier.GlyzDyadicInput
import PlanarNikodym.Analysis.Fourier.GlyzCurveScaleIteration

/-! Actual input-piece integral energies with summable L1 errors.
The refinement sums conserve the input mass, so the number of parents
does not multiply the remainder at any scale. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal ContDiff
namespace PlanarNikodym

theorem glyz_ennreal_sum_rpow_le_rpow_sum {ι : Type*} (I : Finset ι)
    (a : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ I, a i ^ p) ≤ (∑ i ∈ I, a i) ^ p := by
  have he (x : ℝ≥0∞) : x ^ p = x * x ^ (p - 1) := by
    have hsplit : p = 1 + (p - 1) := by ring
    conv_lhs => rw [hsplit]
    rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (sub_nonneg.mpr hp), ENNReal.rpow_one]
  simp_rw [he]
  calc
    _ ≤ ∑ i ∈ I, a i * (∑ j ∈ I, a j) ^ (p - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact Finset.single_le_sum (fun j hj => (zero_le : 0 ≤ a j)) hi
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem glyzDyadicInput_lintegral_enorm_rpow_sum_le {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (2 ^ n), (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ p) ≤
      (∫⁻ y, ‖g y‖ₑ) ^ p := by
  calc
    _ ≤ (∑ i ∈ Finset.range (2 ^ n), ∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ p :=
      glyz_ennreal_sum_rpow_le_rpow_sum _ _ hp
    _ = _ := by rw [glyzDyadicInput_lintegral_enorm_sum hg hs n]

def glyzDyadicKernelPiece {X : Type*} (H : X × Plane → ℂ) (g : Plane → ℂ)
    (n i : ℕ) (x : X) : ℂ := ∫ y, glyzDyadicInput n i g y * H (x, y)

def glyzDyadicKernelEnergy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H : X × Plane → ℂ) (g : Plane → ℂ) (n : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (2 ^ n), ∫⁻ x, ‖glyzDyadicKernelPiece H g n i x‖ₑ ^ p ∂μ

/-- A genuine parent estimate sums to the next full scale with one
L1 error, independent of the number of parent intervals. -/
theorem glyzDyadicKernelEnergy_step {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H : X × Plane → ℂ) {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (n m : ℕ) (hnm : n ≤ m) {p : ℝ} (hp : 1 ≤ p) (D e : ℝ≥0∞)
    (hstep : ∀ i < 2 ^ n,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g n i x‖ₑ ^ p ∂μ) ≤
        D * glyzDyadicBlock (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) m n i +
          e * (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ p) :
    glyzDyadicKernelEnergy μ H g n p ≤ D * glyzDyadicKernelEnergy μ H g m p +
      e * (∫⁻ y, ‖g y‖ₑ) ^ p := by
  unfold glyzDyadicKernelEnergy
  calc
    _ ≤ ∑ i ∈ Finset.range (2 ^ n),
        (D * glyzDyadicBlock (fun j => ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) m n i +
          e * (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ p) :=
      Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = D * (∑ j ∈ Finset.range (2 ^ m), ∫⁻ x, ‖glyzDyadicKernelPiece H g m j x‖ₑ ^ p ∂μ) +
        e * ∑ i ∈ Finset.range (2 ^ n), (∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ) ^ p := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        glyz_sum_dyadic_blocks _ m n hnm]
    _ ≤ _ := by
      gcongr
      exact glyzDyadicInput_lintegral_enorm_rpow_sum_le hg hs n hp

/-- Finite iteration with the exact propagated errors. Every energy
is the integral of the actual kernel applied to the actual input slice. -/
theorem glyzDyadicKernelEnergy_iterate {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H : X × Plane → ℂ) {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (M : ℕ) (n : ℕ → ℕ) {p : ℝ} (hp : 1 ≤ p) (D e : ℕ → ℝ≥0∞)
    (hmono : ∀ j < M, n j ≤ n (j + 1))
    (hstep : ∀ j < M, ∀ i < 2 ^ n j,
      (∫⁻ x, ‖glyzDyadicKernelPiece H g (n j) i x‖ₑ ^ p ∂μ) ≤
        D j * glyzDyadicBlock
          (fun k => ∫⁻ x, ‖glyzDyadicKernelPiece H g (n (j + 1)) k x‖ₑ ^ p ∂μ)
          (n (j + 1)) (n j) i + e j * (∫⁻ y, ‖glyzDyadicInput (n j) i g y‖ₑ) ^ p) :
    glyzDyadicKernelEnergy μ H g (n 0) p ≤
      (∏ j ∈ Finset.range M, D j) * glyzDyadicKernelEnergy μ H g (n M) p +
        (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, D i) * e j) *
          (∫⁻ y, ‖g y‖ₑ) ^ p := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hprev := ih (fun j hj => hmono j (by omega)) (fun j hj => hstep j (by omega))
    have hnext := glyzDyadicKernelEnergy_step μ H hg hs (n M) (n (M + 1))
      (hmono M (by omega)) hp (D M) (e M) (hstep M (by omega))
    calc
      _ ≤ (∏ j ∈ Finset.range M, D j) * glyzDyadicKernelEnergy μ H g (n M) p +
          (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, D i) * e j) *
            (∫⁻ y, ‖g y‖ₑ) ^ p := hprev
      _ ≤ (∏ j ∈ Finset.range M, D j) *
          (D M * glyzDyadicKernelEnergy μ H g (n (M + 1)) p + e M * (∫⁻ y, ‖g y‖ₑ) ^ p) +
          (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, D i) * e j) *
            (∫⁻ y, ‖g y‖ₑ) ^ p := by gcongr
      _ = _ := by rw [Finset.prod_range_succ, Finset.sum_range_succ]; ring

/-- The actual integral pieces are smooth even though the input
restrictions are merely measurable. -/
theorem contDiff_glyzDyadicKernelPiece {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g) (n i : ℕ) :
    ContDiff ℝ ∞ (glyzDyadicKernelPiece H g n i) :=
  contDiff_integral_compactKernel_smul volume (integrable_glyzDyadicInput hg n i) hH hc

/-- Counting the descendants supplies the initial and terminal trivial
Lp estimates for the same genuine integral operator. -/
theorem glyzDyadicKernelPiece_power_refine {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g) (n q i : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖glyzDyadicKernelPiece H g n i x‖ₑ ^ p ∂μ) ≤
      ((2 ^ q : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ∑ j ∈ Finset.range (2 ^ q), ∫⁻ x,
          ‖glyzDyadicKernelPiece H g (n + q) (i * 2 ^ q + j) x‖ₑ ^ p ∂μ := by
  have hm (j : ℕ) : Measurable (fun x =>
      ‖glyzDyadicKernelPiece H g (n + q) (i * 2 ^ q + j) x‖ₑ ^ p) :=
    (contDiff_glyzDyadicKernelPiece hH hc hg _ _).continuous.measurable.enorm.pow_const p
  calc
    _ ≤ ∫⁻ x, ((2 ^ q : ℕ) : ℝ≥0∞) ^ (p - 1) *
        ∑ j ∈ Finset.range (2 ^ q),
          ‖glyzDyadicKernelPiece H g (n + q) (i * 2 ^ q + j) x‖ₑ ^ p ∂μ := by
      apply lintegral_mono
      intro x
      have he : glyzDyadicKernelPiece H g n i x =
          ∑ j ∈ Finset.range (2 ^ q), glyzDyadicKernelPiece H g (n + q) (i * 2 ^ q + j) x :=
        glyz_compactKernel_dyadicInput_refine hg hH hc n q i x
      dsimp only
      rw [he]
      have hpow := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.range (2 ^ q))
        (fun j => ‖glyzDyadicKernelPiece H g (n + q) (i * 2 ^ q + j) x‖ₑ) hp
      exact (ENNReal.rpow_le_rpow (enorm_sum_le _ _) (zero_le_one.trans hp)).trans
        (by simpa only [Finset.card_range] using hpow)
    _ = _ := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun j hj => hm j),
        lintegral_finsetSum _ (fun j hj => hm j)]

theorem glyzDyadicKernelEnergy_initial {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖∫ y, g y * H (x, y)‖ₑ ^ p ∂μ) ≤
      ((2 ^ n : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g n p := by
  have h := glyzDyadicKernelPiece_power_refine μ hH hc hg 0 n 0 hp
  simpa only [glyzDyadicKernelPiece, glyzDyadicInput_zero_of_supported g hs,
    zero_add, zero_mul, glyzDyadicKernelEnergy] using h

theorem glyzDyadicKernelEnergy_trivial_refine {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {H : X × Plane → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {g : Plane → ℂ} (hg : Integrable g)
    (hs : Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1})
    (n m : ℕ) (hnm : n ≤ m) {p : ℝ} (hp : 1 ≤ p) :
    glyzDyadicKernelEnergy μ H g n p ≤
      ((2 ^ (m - n) : ℕ) : ℝ≥0∞) ^ (p - 1) * glyzDyadicKernelEnergy μ H g m p := by
  have h := glyzDyadicKernelEnergy_step μ H hg hs n m hnm hp
    (((2 ^ (m - n) : ℕ) : ℝ≥0∞) ^ (p - 1)) 0 (fun i hi => by
      simpa only [zero_mul, add_zero, glyzDyadicBlock, Nat.add_sub_of_le hnm] using
        glyzDyadicKernelPiece_power_refine μ hH hc hg n (m - n) i hp)
  simpa only [zero_mul, add_zero] using h

end PlanarNikodym
