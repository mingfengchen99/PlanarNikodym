import PlanarNikodym.Analysis.Fourier.MomentPolynomialTranslation

/-! Actual time jets of the normalized model. In particular the full
time-jet parameter Jacobian has determinant one at every time center. -/
noncomputable section
open scoped ContDiff Nat
namespace PlanarNikodym

theorem iteratedDeriv_jetPolynomial_zero {n : ℕ} (w : Aux (n + 1))
    (j : Fin (n + 1)) :
    iteratedDeriv j (jetPolynomial w) 0 = w j := by
  have he : jetPolynomial w = fun t =>
      ∑ i : Fin (n + 1), (w i / ((i : ℕ)! : ℝ)) * t ^ (i : ℕ) := by
    funext t
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, iteratedDeriv_fun_sum (by intro i _; fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    exact div_mul_cancel₀ _ (by positivity)
  · intro i _ hij
    simp only [if_neg (show (j : ℕ) ≠ (i : ℕ) by
      intro h; exact hij (Fin.ext h.symm)), Nat.cast_zero, mul_zero]
  · simp

def momentTimeJet (n : ℕ) (c : ℝ) (w : Aux (n + 1)) : Aux (n + 1) :=
  fun j => iteratedDeriv j (jetPolynomial w) c

theorem momentTimeJet_eq_momentTranslation (n : ℕ) (c : ℝ) :
    momentTimeJet n c = momentTranslation n c := by
  funext w
  ext j
  have he : jetPolynomial (momentTranslation n c w) = fun t => jetPolynomial w (c + t) :=
    funext (jetPolynomial_momentTranslation c w)
  have hj := iteratedDeriv_jetPolynomial_zero (momentTranslation n c w) j
  rw [he, iteratedDeriv_comp_const_add] at hj
  simpa only [momentTimeJet, add_zero] using hj

theorem hasFDerivAt_momentTimeJet (n : ℕ) (c : ℝ) (w : Aux (n + 1)) :
    HasFDerivAt (momentTimeJet n c) (momentTranslation n c).toContinuousLinearMap w := by
  rw [momentTimeJet_eq_momentTranslation]
  exact (momentTranslation n c).hasFDerivAt

theorem det_fderiv_momentTimeJet (n : ℕ) (c : ℝ) (w : Aux (n + 1)) :
    LinearMap.det (fderiv ℝ (momentTimeJet n c) w).toLinearMap = 1 := by
  rw [(hasFDerivAt_momentTimeJet n c w).fderiv]
  exact det_momentTranslation n c

end PlanarNikodym
