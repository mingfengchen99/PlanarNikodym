import PlanarNikodym.Geometry.AnalyticPolynomialDegreeStrata
import PlanarNikodym.Geometry.PolynomialDerivativeClosure

/-! Actual derivatives of monic analytic families are positive constant
multiples of fixed-degree monic analytic families, or identically zero. This
retains the literal derivative-closed family needed in Thom lifting. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weierstrassIteratedDerivativeCoefficients {m : ℕ}
    (a : E → Fin m → ℝ) (k : ℕ) : E → Fin (m - k) → ℝ :=
  polynomialMonicCoefficients (fun x => derivative^[k] (weierstrassPolynomial (a x))) (m - k)

theorem weierstrass_iterated_derivative_top_coeff {m : ℕ} (a : Fin m → ℝ)
    (k : ℕ) (hk : k ≤ m) :
    (derivative^[k] (weierstrassPolynomial a)).coeff (m - k) = (m.descFactorial k : ℝ) := by
  have hc := (weierstrassPolynomial_monic a).coeff_natDegree
  rw [weierstrassPolynomial_natDegree] at hc
  rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, hc, nsmul_eq_mul, mul_one]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weierstrass_iterated_derivative_degree_stratum {m : ℕ} (a : E → Fin m → ℝ)
    (k : ℕ) (hk : k ≤ m) (x : E) :
    x ∈ polynomialDegreeStratum
      (fun y => derivative^[k] (weierstrassPolynomial (a y))) (m - k) := by
  refine ⟨?_, ?_⟩
  · rw [weierstrass_iterated_derivative_top_coeff _ k hk]
    exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
  · intro l hl
    exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_iterate_derivative _ k).trans_lt (by rw [weierstrassPolynomial_natDegree]; exact hl))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weierstrass_iterated_derivative_normalization {m : ℕ} (a : E → Fin m → ℝ)
    (k : ℕ) (x : E) :
    derivative^[k] (weierstrassPolynomial (a x)) =
      C (m.descFactorial k : ℝ) * weierstrassPolynomial (weierstrassIteratedDerivativeCoefficients a k x) := by
  by_cases hk : k ≤ m
  · have he := polynomial_eq_leading_mul_monic_on_stratum
      (fun y => derivative^[k] (weierstrassPolynomial (a y))) (m - k) x
      (weierstrass_iterated_derivative_degree_stratum a k hk x)
    rw [weierstrass_iterated_derivative_top_coeff _ k hk] at he
    exact he
  · have hmk : m < k := Nat.lt_of_not_ge hk
    rw [iterate_derivative_eq_zero (by rw [weierstrassPolynomial_natDegree]; exact hmk),
      Nat.descFactorial_of_lt hmk]
    simp

theorem analyticAt_weierstrassIteratedDerivativeCoefficients {m : ℕ}
    (a : E → Fin m → ℝ) (k : ℕ) (x : E) (ha : AnalyticAt ℝ a x) :
    AnalyticAt ℝ (weierstrassIteratedDerivativeCoefficients a k) x := by
  by_cases hk : k ≤ m
  · apply analyticAt_polynomialMonicCoefficients
    · intro l
      simp only [coeff_iterate_derivative, nsmul_eq_mul]
      exact analyticAt_const.mul (analyticAt_weierstrassPolynomial_coeff a x ha (l + k))
    · rw [weierstrass_iterated_derivative_top_coeff _ k hk]
      exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
  · apply analyticAt_pi_iff.mpr
    intro i
    have hi := i.isLt
    omega

theorem oneDimensionalSign_mul_of_pos (c : ℝ) (hc : 0 < c) (r : ℝ) :
    oneDimensionalSign (c * r) = oneDimensionalSign r := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [oneDimensionalSign_eq_zero.mpr (mul_neg_of_pos_of_neg hc hr),
      oneDimensionalSign_eq_zero.mpr hr]
  · simp only [hr, mul_zero]
  · rw [oneDimensionalSign_eq_two.mpr (mul_pos hc hr), oneDimensionalSign_eq_two.mpr hr]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Normalization changes no strict sign on any nonzero derivative; the
remaining derivatives are literally the zero polynomial on every parameter. -/
theorem weierstrass_iterated_derivative_sign {m : ℕ} (a : E → Fin m → ℝ)
    (k : ℕ) (x : E) (t : ℝ) :
    if k ≤ m then
      oneDimensionalSign ((derivative^[k] (weierstrassPolynomial (a x))).eval t) =
        oneDimensionalSign ((weierstrassPolynomial (weierstrassIteratedDerivativeCoefficients a k x)).eval t)
    else derivative^[k] (weierstrassPolynomial (a x)) = 0 := by
  split_ifs with hk
  · rw [weierstrass_iterated_derivative_normalization, eval_mul, eval_C]
    apply oneDimensionalSign_mul_of_pos
    exact_mod_cast Nat.descFactorial_pos.mpr hk
  · exact iterate_derivative_eq_zero (by rw [weierstrassPolynomial_natDegree]; omega)

end PlanarNikodym
