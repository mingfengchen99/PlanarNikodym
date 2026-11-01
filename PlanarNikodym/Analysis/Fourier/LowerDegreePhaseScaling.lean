import PlanarNikodym.Analysis.Fourier.CoefficientDilation
import PlanarNikodym.Analysis.Fourier.TaylorJetNondegeneracy
import PlanarNikodym.Analysis.Fourier.TaylorPhaseReduction
import Mathlib.Algebra.BigOperators.Fin

/-! Anisotropic scaling of the actual Taylor coefficients. It turns a
time slice into the unit interval with effective frequency `r * δ^n`.
The diagonal maps and their measure factors are genuine maps. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Nat

namespace PlanarNikodym

def jetPolynomial {n : ℕ} (a : Fin (n + 1) → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, a i * τ ^ (i : ℕ) / ((i : ℕ)! : ℝ)

def lowerDegreeWeight (n : ℕ) (δ : ℝ) (i : Fin (n + 1)) : ℝ := δ ^ (i : ℕ) / δ ^ n

theorem lowerDegreeWeight_ne_zero (n : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (i : Fin (n + 1)) :
    lowerDegreeWeight n δ i ≠ 0 := div_ne_zero (pow_ne_zero _ hδ) (pow_ne_zero _ hδ)

theorem lowerDegreeWeight_pos (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (i : Fin (n + 1)) :
    0 < lowerDegreeWeight n δ i := div_pos (pow_pos hδ _) (pow_pos hδ _)

theorem one_le_lowerDegreeWeight (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (i : Fin (n + 1)) : 1 ≤ lowerDegreeWeight n δ i := by
  exact (one_le_div (pow_pos hδ n)).mpr
    (pow_le_pow_of_le_one hδ.le hδ₁ (Nat.le_of_lt_succ i.isLt))

def lowerDegreeDilation (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  coefficientDilation (lowerDegreeWeight n δ) (lowerDegreeWeight_ne_zero n hδ)

@[simp] theorem lowerDegreeDilation_apply (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    lowerDegreeDilation n δ hδ a i = (δ ^ (i : ℕ) / δ ^ n) * a i := rfl

theorem jetPolynomial_time_rescale (n : ℕ) {δ : ℝ} (hδ : δ ≠ 0)
    (a : Fin (n + 1) → ℝ) (τ : ℝ) :
    jetPolynomial a (δ * τ) = δ ^ n * jetPolynomial (lowerDegreeDilation n δ hδ a) τ := by
  unfold jetPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [lowerDegreeDilation_apply, mul_pow]
  field_simp

theorem timeTaylorEval_eq_jetPolynomial {P : Type} (Φ : P × ℝ → ℝ)
    (n : ℕ) (p : P) (c t : ℝ) :
    timeTaylorEval Φ n p c t =
      jetPolynomial (fun i : Fin (n + 1) => iteratedDeriv i (fun s => Φ (p, s)) c) (t - c) := by
  unfold timeTaylorEval jetPolynomial
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    iteratedDeriv i (fun s => Φ (p, s)) c * (t - c) ^ i / (i ! : ℝ)) (n + 1)).symm

/-- Exact lower-degree phase identity in the original Taylor phase,
including the resulting effective frequency. -/
theorem frequency_timeTaylorEval_rescale {P : Type} (Φ : P × ℝ → ℝ)
    (n : ℕ) (p : P) (c τ r η : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    r * η * timeTaylorEval Φ n p c (c + δ * τ) =
      (r * δ ^ n) * η * jetPolynomial (lowerDegreeDilation n δ hδ
        (fun i : Fin (n + 1) => iteratedDeriv i (fun s => Φ (p, s)) c)) τ := by
  rw [timeTaylorEval_eq_jetPolynomial, add_sub_cancel_left, jetPolynomial_time_rescale n hδ]
  ring

theorem det_lowerDegreeDilation (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    LinearMap.det (lowerDegreeDilation n δ hδ).toLinearMap =
      ∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n :=
  det_coefficientDilation _ _

theorem integral_comp_lowerDegreeDilation (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (F : (Fin (n + 1) → ℝ) → ℂ) :
    (∫ a, F (lowerDegreeDilation n δ hδ a)) =
      |(∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n)⁻¹| • ∫ b, F b :=
  integral_comp_coefficientDilation _ _ F

/-- The inverse anisotropic coefficient map is a contraction, even
though the forward image boxes expand as the time scale decreases. -/
theorem norm_lowerDegreeDilation_symm_le_one (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ‖(lowerDegreeDilation n δ hδ.ne').symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  change ‖(lowerDegreeWeight n δ i)⁻¹ * x i‖ ≤ ‖x‖
  rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos (lowerDegreeWeight_pos n hδ i)]
  calc
    _ ≤ 1 * |x i| := mul_le_mul_of_nonneg_right
      (inv_le_one_of_one_le₀ (one_le_lowerDegreeWeight n hδ hδ₁ i)) (abs_nonneg _)
    _ ≤ ‖x‖ := by simpa only [one_mul, ← Real.norm_eq_abs] using norm_le_pi_norm x i

/-- All actual jets of a smooth amplitude composed with the inverse
anisotropic map obey the same bound as its original jets. -/
theorem norm_iteratedFDeriv_comp_lowerDegreeDilation_symm_le (n m : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) {f : (Fin (n + 1) → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : Fin (n + 1) → ℝ) :
    ‖iteratedFDeriv ℝ m (fun y => f ((lowerDegreeDilation n δ hδ.ne').symm y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f ((lowerDegreeDilation n δ hδ.ne').symm x)‖ := by
  let D := (lowerDegreeDilation n δ hδ.ne').symm.toContinuousLinearMap
  have hcomp := D.iteratedFDeriv_comp_right (contDiff_infty.mp hf m) x (i := m) le_rfl
  dsimp only [Function.comp_def] at hcomp
  change ‖iteratedFDeriv ℝ m (fun y => f (D y)) x‖ ≤ ‖iteratedFDeriv ℝ m f (D x)‖
  rw [hcomp]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f (D x)‖ * ∏ _ : Fin m, ‖D‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ m f (D x)‖ * 1 := mul_le_mul_of_nonneg_left
      (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ =>
        norm_lowerDegreeDilation_symm_le_one n hδ hδ₁)) (norm_nonneg _)
    _ = _ := mul_one _

theorem critical_effective_frequency_eq_inv_scale (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r * criticalTimeScale n r ^ n = (criticalTimeScale n r)⁻¹ := by
  have hδ := (criticalTimeScale_pos n hr).ne'
  have hfreq := frequency_mul_criticalTimeScale_pow n hr
  rw [← one_div]
  apply (eq_div_iff hδ).mpr
  simpa only [pow_succ, mul_assoc] using hfreq

theorem critical_effective_frequency_ge_one (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    1 ≤ r * criticalTimeScale n r ^ n := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [critical_effective_frequency_eq_inv_scale n hrpos]
  exact (one_le_inv₀ (criticalTimeScale_pos n hrpos)).mpr (criticalTimeScale_le_one n hr)

end PlanarNikodym
