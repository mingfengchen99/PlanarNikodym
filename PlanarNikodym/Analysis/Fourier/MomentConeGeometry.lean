import PlanarNikodym.Analysis.Fourier.LowerDegreePhaseScaling
import Mathlib.LinearAlgebra.Vandermonde

/-! The normalized moment curve underlying constant-coefficient conic
decoupling. These are actual geometric statements, not a decoupling
assumption: the sampling determinant, its nonvanishing, and a quantitative
lower bound for separated time parameters. -/

noncomputable section
open scoped BigOperators Nat

namespace PlanarNikodym

def momentCurve (n : ℕ) (t : ℝ) : Aux (n + 1) :=
  fun j => t ^ (j : ℕ) / ((j : ℕ)! : ℝ)

def momentCone (n : ℕ) (t η : ℝ) : Aux (n + 1) := η • momentCurve n t

theorem jetPolynomial_eq_pairing {n : ℕ} (w : Aux (n + 1)) (t : ℝ) :
    jetPolynomial w t = ∑ j, w j * momentCurve n t j := by
  simp only [jetPolynomial, momentCurve, mul_div_assoc]

theorem frequency_jetPolynomial_eq_cone_pairing {n : ℕ}
    (w : Aux (n + 1)) (t η R : ℝ) :
    R * η * jetPolynomial w t = R * ∑ j, w j * momentCone n t η j := by
  rw [jetPolynomial_eq_pairing]
  simp only [momentCone, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def momentSamplingMatrix {n : ℕ} (t : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => momentCurve n (t i) j

theorem momentSamplingMatrix_eq {n : ℕ} (t : Fin (n + 1) → ℝ) :
    momentSamplingMatrix t = Matrix.vandermonde t *
      Matrix.diagonal (fun j : Fin (n + 1) => (((j : ℕ)! : ℝ))⁻¹) := by
  ext i j
  simp [momentSamplingMatrix, momentCurve, Matrix.mul_diagonal, div_eq_mul_inv]

theorem det_momentSamplingMatrix {n : ℕ} (t : Fin (n + 1) → ℝ) :
    (momentSamplingMatrix t).det =
      (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (t j - t i)) *
        ∏ j : Fin (n + 1), (((j : ℕ)! : ℝ))⁻¹ := by
  rw [momentSamplingMatrix_eq, Matrix.det_mul, Matrix.det_vandermonde, Matrix.det_diagonal]

theorem det_momentSamplingMatrix_ne_zero_iff {n : ℕ} (t : Fin (n + 1) → ℝ) :
    (momentSamplingMatrix t).det ≠ 0 ↔ Function.Injective t := by
  rw [momentSamplingMatrix_eq, Matrix.det_mul, Matrix.det_diagonal]
  have h : (∏ j : Fin (n + 1), (((j : ℕ)! : ℝ))⁻¹) ≠ 0 := by positivity
  rw [mul_ne_zero_iff, and_iff_left h, Matrix.det_vandermonde_ne_zero_iff]

/-- The positive normalization in the quantitative transversality bound. -/
def momentFactorialConstant (n : ℕ) : ℝ :=
  ∏ j : Fin (n + 1), (((j : ℕ)! : ℝ))⁻¹

theorem momentFactorialConstant_pos (n : ℕ) : 0 < momentFactorialConstant n := by
  unfold momentFactorialConstant
  positivity

/-- A separated list gives an explicit lower bound. The nested product
retains exactly one factor for each pair; it has no hidden dependence on
the particular time parameters. -/
theorem abs_det_momentSamplingMatrix_lower_bound {n : ℕ}
    (t : Fin (n + 1) → ℝ) {ν : ℝ} (hν : 0 ≤ ν)
    (hsep : ∀ i j : Fin (n + 1), i < j → ν ≤ |t j - t i|) :
    momentFactorialConstant n * (∏ i : Fin (n + 1), ν ^ (Finset.Ioi i).card) ≤
      |(momentSamplingMatrix t).det| := by
  rw [det_momentSamplingMatrix, abs_mul]
  change momentFactorialConstant n * _ ≤ _ * |momentFactorialConstant n|
  rw [abs_of_pos (momentFactorialConstant_pos n)]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ (momentFactorialConstant_pos n).le
  simp_rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact pow_nonneg hν _
  · intro i _
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hν)
      (fun j hj => hsep i j (Finset.mem_Ioi.mp hj))

end PlanarNikodym
