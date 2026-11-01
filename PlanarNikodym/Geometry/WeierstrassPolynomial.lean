import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Real.Basic

/-! The actual monic polynomial associated to a Weierstrass coefficient vector,
and the uniform bound on its distinct real roots, including degree zero. -/
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace PlanarNikodym

def weierstrassPolynomial {m : ℕ} (a : Fin m → ℝ) : ℝ[X] :=
  X ^ m + ∑ i : Fin m, C (a i) * X ^ (i : ℕ)

@[simp] theorem weierstrassPolynomial_eval {m : ℕ} (a : Fin m → ℝ) (t : ℝ) :
    (weierstrassPolynomial a).eval t = t ^ m + ∑ i : Fin m, a i * t ^ (i : ℕ) := by
  simp [weierstrassPolynomial, eval_finsetSum]

theorem weierstrassPolynomial_monic {m : ℕ} (a : Fin m → ℝ) :
    (weierstrassPolynomial a).Monic := by
  apply (monic_X_pow m).add_of_left
  simpa only [degree_X_pow] using degree_sum_fin_lt a

@[simp] theorem weierstrassPolynomial_natDegree {m : ℕ} (a : Fin m → ℝ) :
    (weierstrassPolynomial a).natDegree = m := by
  rw [weierstrassPolynomial, natDegree_add_eq_left_of_degree_lt]
  · exact natDegree_X_pow m
  · simpa only [degree_X_pow] using degree_sum_fin_lt a

/-- Translation does not change the upper bound on the number of distinct roots. -/
theorem weierstrassPolynomial_finite_roots {m : ℕ} (a : Fin m → ℝ) (t₀ : ℝ) :
    {t : ℝ | (t - t₀) ^ m + ∑ i : Fin m, a i * (t - t₀) ^ (i : ℕ) = 0}.Finite ∧
    {t : ℝ | (t - t₀) ^ m + ∑ i : Fin m, a i * (t - t₀) ^ (i : ℕ) = 0}.ncard ≤ m := by
  let P := weierstrassPolynomial a
  have hset : {t : ℝ | (t - t₀) ^ m + ∑ i : Fin m, a i * (t - t₀) ^ (i : ℕ) = 0} =
      (fun t : ℝ => t + t₀) '' P.rootSet ℝ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨t - t₀, ?_, sub_add_cancel _ _⟩
      rw [(weierstrassPolynomial_monic a).mem_rootSet]
      simpa [P, aeval_def] using h
    · rintro ⟨r, hr, rfl⟩
      rw [(weierstrassPolynomial_monic a).mem_rootSet] at hr
      simpa [P, aeval_def] using hr
  rw [hset]
  refine ⟨(P.rootSet_finite ℝ).image _, ?_⟩
  calc
    _ ≤ (P.rootSet ℝ).ncard := Set.ncard_image_le (P.rootSet_finite ℝ)
    _ ≤ P.natDegree := P.ncard_rootSet_le ℝ
    _ = m := weierstrassPolynomial_natDegree a

end PlanarNikodym
