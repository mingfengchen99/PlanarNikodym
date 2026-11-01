import PlanarNikodym.Analysis.Fourier.MomentPolynomialTranslation
import Mathlib.Algebra.BigOperators.Intervals

/-! Parabolic rescaling of the constant-coefficient cone, with exact
phase and determinant factors. The center is arbitrary. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Nat
namespace PlanarNikodym

def momentParabolicMap (n : ℕ) (c δ : ℝ) (hδ : δ ≠ 0) :
    Aux (n + 1) ≃L[ℝ] Aux (n + 1) :=
  (momentTranslation n c).trans (lowerDegreeDilation n δ hδ)

theorem jetPolynomial_parabolic_rescale {n : ℕ} (w : Aux (n + 1))
    (c δ t : ℝ) (hδ : δ ≠ 0) :
    jetPolynomial w (c + δ * t) =
      δ ^ n * jetPolynomial (momentParabolicMap n c δ hδ w) t := by
  rw [← jetPolynomial_momentTranslation c w, jetPolynomial_time_rescale n hδ]
  rfl

theorem det_momentParabolicMap (n : ℕ) (c δ : ℝ) (hδ : δ ≠ 0) :
    LinearMap.det (momentParabolicMap n c δ hδ).toLinearMap =
      ∏ j : Fin (n + 1), δ ^ (j : ℕ) / δ ^ n := by
  change LinearMap.det ((lowerDegreeDilation n δ hδ).toLinearMap.comp
    (momentTranslation n c).toLinearMap) = _
  rw [LinearMap.det_comp, det_momentTranslation, mul_one, det_lowerDegreeDilation]

theorem sum_moment_weights (n : ℕ) :
    (∑ j : Fin (n + 1), (j : ℕ)) = n * (n + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j) (n + 1), Finset.sum_range_id]
  simp only [Nat.add_sub_cancel, Nat.mul_comm]

theorem det_momentParabolicMap_eq (n : ℕ) (c δ : ℝ) (hδ : δ ≠ 0) :
    LinearMap.det (momentParabolicMap n c δ hδ).toLinearMap =
      (δ⁻¹) ^ (n * (n + 1) / 2) := by
  rw [det_momentParabolicMap, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs : (∑ j : Fin (n + 1), (j : ℕ)) * 2 = n * (n + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j) (n + 1)]
    simpa only [Nat.add_sub_cancel, Nat.mul_comm] using Finset.sum_range_id_mul_two (n + 1)
  have hdegree : n * (n + 1) =
      (∑ j : Fin (n + 1), (j : ℕ)) + ∑ j : Fin (n + 1), (j : ℕ) := by omega
  conv_lhs => arg 2; rw [← pow_mul, hdegree, pow_add]
  rw [sum_moment_weights, inv_pow]
  field_simp

theorem map_momentParabolicMap_volume (n : ℕ) (c δ : ℝ) (hδ : δ ≠ 0) :
    Measure.map (momentParabolicMap n c δ hδ) volume =
      ENNReal.ofReal (|δ| ^ (n * (n + 1) / 2)) •
        (volume : Measure (Aux (n + 1))) := by
  have hd : LinearMap.det (momentParabolicMap n c δ hδ).toLinearMap ≠ 0 := by
    rw [det_momentParabolicMap_eq]
    exact pow_ne_zero _ (inv_ne_zero hδ)
  change Measure.map (momentParabolicMap n c δ hδ).toLinearMap volume = _
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hd, det_momentParabolicMap_eq,
    ← inv_pow, inv_inv, abs_pow]

end PlanarNikodym
