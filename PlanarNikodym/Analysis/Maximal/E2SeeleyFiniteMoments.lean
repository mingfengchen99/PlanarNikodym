import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! Actual finite moment-correcting blocks for a Seeley extension.
The coefficients are extracted from Lagrange basis polynomials at the
negative nodes −1,…,−(n+1); their moments vanish below order n and equal
one at order n. No interpolation coefficients are postulated. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace PlanarNikodym

def e2SeeleyNode (n : ℕ) (k : Fin (n + 1)) : ℝ := -((k.val : ℝ) + 1)

theorem e2SeeleyNode_neg (n : ℕ) (k : Fin (n + 1)) : e2SeeleyNode n k < 0 := by
  unfold e2SeeleyNode
  linarith [Nat.cast_nonneg k.val (α := ℝ)]

theorem e2SeeleyNode_injective (n : ℕ) : Function.Injective (e2SeeleyNode n) := by
  intro i j hij
  apply Fin.ext
  unfold e2SeeleyNode at hij
  exact_mod_cast (by linarith : (i.val : ℝ) = j.val)

def e2SeeleyMomentCoefficient (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (e2SeeleyNode n) k).coeff n

theorem e2SeeleyMomentCoefficient_moment (n j : ℕ) (hj : j ≤ n) :
    ∑ k : Fin (n + 1), e2SeeleyMomentCoefficient n k * (e2SeeleyNode n k) ^ j =
      if j = n then 1 else 0 := by
  have hp : (X ^ j : ℝ[X]) =
      Lagrange.interpolate Finset.univ (e2SeeleyNode n) (fun k => (e2SeeleyNode n k) ^ j) := by
    have hdeg : (X ^ j : ℝ[X]).degree < (Finset.univ : Finset (Fin (n + 1))).card := by
      simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast (Nat.lt_succ_of_le hj)
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
      (Lagrange.eq_interpolate ((e2SeeleyNode_injective n).injOn) hdeg)
  have hc := congrArg (fun P : ℝ[X] => P.coeff n) hp
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow] at hc
  calc
    _ = ∑ k : Fin (n + 1), (e2SeeleyNode n k) ^ j *
        (Lagrange.basis Finset.univ (e2SeeleyNode n) k).coeff n := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [e2SeeleyMomentCoefficient]
      ring
    _ = if n = j then 1 else 0 := hc.symm
    _ = _ := by
      by_cases h : j = n
      · subst j; simp
      · simp [h, Ne.symm h]

theorem e2SeeleyMomentCoefficient_low (n j : ℕ) (hj : j < n) :
    ∑ k : Fin (n + 1), e2SeeleyMomentCoefficient n k * (e2SeeleyNode n k) ^ j = 0 := by
  rw [e2SeeleyMomentCoefficient_moment n j hj.le, if_neg (Nat.ne_of_lt hj)]

@[simp] theorem e2SeeleyMomentCoefficient_top (n : ℕ) :
    ∑ k : Fin (n + 1), e2SeeleyMomentCoefficient n k * (e2SeeleyNode n k) ^ n = 1 := by
  rw [e2SeeleyMomentCoefficient_moment n n le_rfl, if_pos rfl]

end PlanarNikodym
