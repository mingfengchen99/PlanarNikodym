import PlanarNikodym.Analysis.Fourier.MomentModelJets
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Two-point Hermite uniqueness for the actual polynomial Taylor jets.
This is the algebraic injectivity underlying GLYZ's mixed-jet geometry. -/

noncomputable section
open Polynomial

namespace PlanarNikodym

theorem iteratedDeriv_polynomial_eval (p : ℝ[X]) (j : ℕ) :
    iteratedDeriv j (fun x => p.eval x) = fun x => (Polynomial.derivative^[j] p).eval x := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ', show deriv (fun x => p.eval x) =
      (fun x => p.derivative.eval x) from funext (fun x => p.deriv)]
    rw [ih, Function.iterate_succ_apply]

theorem iteratedDeriv_polynomial_eval_eq_taylor (p : ℝ[X]) (j : ℕ) (s : ℝ) :
    iteratedDeriv j (fun x => p.eval x) s =
      (j.factorial : ℝ) * (Polynomial.taylor s p).coeff j := by
  rw [iteratedDeriv_polynomial_eval, Polynomial.taylor_coeff,
    ← Polynomial.factorial_smul_hasseDeriv]
  simp

theorem polynomial_X_sub_C_pow_dvd_of_taylor_zero (p : ℝ[X]) (s : ℝ) (l : ℕ)
    (h : ∀ j < l, (Polynomial.taylor s p).coeff j = 0) :
    (X - C s) ^ l ∣ p := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, ← Polynomial.taylor_apply, Polynomial.X_pow_dvd_iff]
  exact h

/-- Vanishing Taylor jets at two distinct points force a polynomial of
strictly smaller total degree to vanish. Both zero-size blocks are allowed. -/
theorem polynomial_eq_zero_of_two_taylor_jets (p : ℝ[X]) {l r : ℕ} {s t : ℝ}
    (hst : s ≠ t) (hp : p.degree < (l + r : ℕ))
    (hs : ∀ j < l, (Polynomial.taylor s p).coeff j = 0)
    (ht : ∀ j < r, (Polynomial.taylor t p).coeff j = 0) : p = 0 := by
  have hcop : IsCoprime (X - C s : ℝ[X]) (X - C t) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hst).isUnit
  have hd : (X - C s) ^ l * (X - C t) ^ r ∣ p :=
    hcop.pow.mul_dvd
      (polynomial_X_sub_C_pow_dvd_of_taylor_zero p s l hs)
      (polynomial_X_sub_C_pow_dvd_of_taylor_zero p t r ht)
  by_contra hn
  have hdeg := Polynomial.degree_le_of_dvd hd hn
  have he : ((X - C s : ℝ[X]) ^ l * (X - C t) ^ r).degree =
      ((l + r : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_pow, Polynomial.degree_pow,
      Polynomial.degree_X_sub_C, Polynomial.degree_X_sub_C]
    simp
  rw [he] at hdeg
  exact (not_lt_of_ge hdeg) hp

def mixedTaylorJetMap (l r : ℕ) (s t : ℝ) :
    Polynomial.degreeLT ℝ (l + r) →ₗ[ℝ] (Aux l × Aux r) where
  toFun p := (fun j => (Polynomial.taylor s p.1).coeff j,
    fun j => (Polynomial.taylor t p.1).coeff j)
  map_add' := by intro p q; ext j <;> simp
  map_smul' := by intro c p; ext j <;> simp

theorem mixedTaylorJetMap_injective (l r : ℕ) {s t : ℝ} (hst : s ≠ t) :
    Function.Injective (mixedTaylorJetMap l r s t) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  apply Subtype.ext
  apply polynomial_eq_zero_of_two_taylor_jets p.1 hst (Polynomial.mem_degreeLT.mp p.2)
  · intro j hj
    exact congrFun (congrArg Prod.fst hp) ⟨j, hj⟩
  · intro j hj
    exact congrFun (congrArg Prod.snd hp) ⟨j, hj⟩

/-- The actual mixed Taylor map is a linear equivalence, constructed
from injectivity and the equality of its finite dimensions. -/
def mixedTaylorJetEquiv (l r : ℕ) (s t : ℝ) (hst : s ≠ t) :
    Polynomial.degreeLT ℝ (l + r) ≃ₗ[ℝ] (Aux l × Aux r) :=
  LinearEquiv.ofBijective (mixedTaylorJetMap l r s t)
    ⟨mixedTaylorJetMap_injective l r hst, by
      apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
        (mixedTaylorJetMap_injective l r hst)
      rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (l + r))]
      simp⟩

end PlanarNikodym
