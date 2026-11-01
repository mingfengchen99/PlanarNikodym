import PlanarNikodym.Geometry.AnalyticPolynomialResultant
import PlanarNikodym.Geometry.WeierstrassPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Actual analytic collision determinants for monic Weierstrass polynomials.
The determinant has the fixed Sylvester size `m + (m-1)`, including degree
zero, and agrees up to the usual sign with the polynomial discriminant. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology

namespace PlanarNikodym

def weierstrassCollisionDet {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  (weierstrassPolynomial a).resultant (weierstrassPolynomial a).derivative m (m - 1)

theorem weierstrassCollisionDet_eq_discr {m : ℕ} (a : Fin m → ℝ) :
    weierstrassCollisionDet a =
      (-1 : ℝ) ^ (m * (m - 1) / 2) * (weierstrassPolynomial a).discr := by
  by_cases hm : m = 0
  · subst m
    have he : weierstrassPolynomial a = Polynomial.C (1 : ℝ) := by
      simp [weierstrassPolynomial]
    have hd : (1 : ℝ[X]).discr = 1 := by
      simpa only [Polynomial.C_1] using Polynomial.discr_C (1 : ℝ)
    simp [weierstrassCollisionDet, he, hd]
  · have hp : 0 < (weierstrassPolynomial a).degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (by
        rw [weierstrassPolynomial_natDegree]
        exact Nat.pos_of_ne_zero hm)
    simpa only [weierstrassCollisionDet, weierstrassPolynomial_natDegree,
      (weierstrassPolynomial_monic a).leadingCoeff, mul_one]
      using (Polynomial.resultant_deriv hp)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_weierstrassPolynomial_coeff
    {m : ℕ} (a : E → Fin m → ℝ) (x : E) (ha : AnalyticAt ℝ a x) (k : ℕ) :
    AnalyticAt ℝ (fun y => (weierstrassPolynomial (a y)).coeff k) x := by
  simp only [weierstrassPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul]
  apply analyticAt_const.add
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (analyticAt_pi_iff.mp ha i).mul analyticAt_const

theorem analyticAt_weierstrassCollisionDet
    {m : ℕ} (a : E → Fin m → ℝ) (x : E) (ha : AnalyticAt ℝ a x) :
    AnalyticAt ℝ (fun y => weierstrassCollisionDet (a y)) x := by
  apply analyticAt_polynomial_resultant
  · exact analyticAt_weierstrassPolynomial_coeff a x ha
  · intro k
    simp only [Polynomial.coeff_derivative]
    exact (analyticAt_weierstrassPolynomial_coeff a x ha (k + 1)).mul analyticAt_const

/-- The actual Mathlib polynomial discriminant is analytic, without any
assumption that it is nonzero or that the roots are already simple. -/
theorem analyticAt_weierstrassPolynomial_discr
    {m : ℕ} (a : E → Fin m → ℝ) (x : E) (ha : AnalyticAt ℝ a x) :
    AnalyticAt ℝ (fun y => (weierstrassPolynomial (a y)).discr) x := by
  have hn : (-1 : ℝ) ^ (m * (m - 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have he (y : E) : (weierstrassPolynomial (a y)).discr =
      weierstrassCollisionDet (a y) / (-1 : ℝ) ^ (m * (m - 1) / 2) := by
    apply (eq_div_iff hn).mpr
    rw [weierstrassCollisionDet_eq_discr]
    ring
  simp_rw [he]
  exact (analyticAt_weierstrassCollisionDet a x ha).div analyticAt_const hn

/-- Every real root is simple whenever the actual collision determinant is
nonzero. The derivative is the actual derivative of polynomial evaluation. -/
theorem deriv_ne_zero_of_weierstrassCollisionDet_ne_zero
    {m : ℕ} (a : Fin m → ℝ) (hdet : weierstrassCollisionDet a ≠ 0)
    (t : ℝ) (ht : (weierstrassPolynomial a).eval t = 0) :
    deriv (fun s => (weierstrassPolynomial a).eval s) t ≠ 0 := by
  by_cases hm : m = 0
  · subst m
    simp [weierstrassPolynomial] at ht
  · rw [Polynomial.deriv]
    intro hd
    apply polynomial_no_common_root_of_resultant_ne_zero
      (weierstrassPolynomial a) (weierstrassPolynomial a).derivative m (m - 1)
      (by simp) (by simpa only [weierstrassPolynomial_natDegree]
        using Polynomial.natDegree_derivative_le (weierstrassPolynomial a))
      (Or.inl hm) hdet t ⟨ht, hd⟩

/-- Every actual multiple real root lies in the analytic discriminant locus. -/
theorem weierstrassCollisionDet_eq_zero_of_multiple_root
    {m : ℕ} (a : Fin m → ℝ) (t : ℝ)
    (ht : (weierstrassPolynomial a).eval t = 0)
    (hd : deriv (fun s => (weierstrassPolynomial a).eval s) t = 0) :
    weierstrassCollisionDet a = 0 := by
  by_contra h
  exact (deriv_ne_zero_of_weierstrassCollisionDet_ne_zero a h t ht) hd

/-- The pairwise collision resultant for two monic coefficient vectors. -/
def weierstrassPairResultant {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ) : ℝ :=
  (weierstrassPolynomial a).resultant (weierstrassPolynomial b) m n

theorem analyticAt_weierstrassPairResultant
    {m n : ℕ} (a : E → Fin m → ℝ) (b : E → Fin n → ℝ) (x : E)
    (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x) :
    AnalyticAt ℝ (fun y => weierstrassPairResultant (a y) (b y)) x :=
  analyticAt_polynomial_resultant _ _ m n x
    (analyticAt_weierstrassPolynomial_coeff a x ha)
    (analyticAt_weierstrassPolynomial_coeff b x hb)

/-- Nonzero pairwise resultant excludes shared real roots. Unlike arbitrary
polynomials, the degree-zero monic polynomial is one, so there is no exception
to the statement when one or both degrees are zero. -/
theorem no_common_root_of_weierstrassPairResultant_ne_zero
    {m n : ℕ} (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hres : weierstrassPairResultant a b ≠ 0) :
    ∀ t : ℝ, ¬ ((weierstrassPolynomial a).eval t = 0 ∧
      (weierstrassPolynomial b).eval t = 0) := by
  by_cases hm : m = 0
  · subst m
    intro t ht
    have h := ht.1
    simp [weierstrassPolynomial] at h
  · exact polynomial_no_common_root_of_resultant_ne_zero
      (weierstrassPolynomial a) (weierstrassPolynomial b) m n
      (by simp) (by simp) (Or.inl hm) hres

end PlanarNikodym
