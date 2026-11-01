import PlanarNikodym.Geometry.AnalyticPolynomialRootStrata

/-! Finite root strata for an arbitrary finite family of analytic monic
polynomials. Repeated roots and shared factors are allowed. The coefficients
of the actual product are proved analytic from the original coefficient
functions, and its complete real zero set is the union of the member zero sets.
The additional analytic graph tests record membership in individual members;
their zero sets need not be entire root graphs. -/

noncomputable section
open Set Polynomial
open scoped Topology BigOperators

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every coefficient of a finite product is analytic when the coefficients
of the factors are analytic. No degree bound is needed for this local claim. -/
theorem analyticAt_polynomial_finset_prod_coeff
    {J : Type*} (s : Finset J) (P : J → E → ℝ[X]) (x : E)
    (hP : ∀ j ∈ s, ∀ k, AnalyticAt ℝ (fun y => (P j y).coeff k) x) (k : ℕ) :
    AnalyticAt ℝ (fun y => (∏ j ∈ s, P j y).coeff k) x := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa only [Finset.prod_empty] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : E => (1 : ℝ[X]).coeff k) x)
  | @insert j s hj ih =>
      simp only [Finset.prod_insert hj, Polynomial.coeff_mul]
      apply Finset.analyticAt_fun_sum
      intro v _
      exact (hP j (Finset.mem_insert_self _ _) v.1).mul
        (ih (fun i hi => hP i (Finset.mem_insert_of_mem hi)) v.2)

/-- The lower coefficient vector of the actual finite product. -/
def weierstrassFamilyProductCoefficients
    {J : Type*} [Fintype J] (m : J → ℕ)
    (a : E → ∀ j, Fin (m j) → ℝ) : E → Fin (∑ j, m j) → ℝ :=
  fun x i => (∏ j, weierstrassPolynomial (a x j)).coeff i

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem weierstrassPolynomial_familyProductCoefficients
    {J : Type*} [Fintype J] (m : J → ℕ)
    (a : E → ∀ j, Fin (m j) → ℝ) (x : E) :
    weierstrassPolynomial (weierstrassFamilyProductCoefficients m a x) =
      ∏ j, weierstrassPolynomial (a x j) := by
  classical
  let P := ∏ j, weierstrassPolynomial (a x j)
  have hm (j : J) (_ : j ∈ Finset.univ) :
      (weierstrassPolynomial (a x j)).Monic :=
    weierstrassPolynomial_monic _
  have hP : P.Monic := Polynomial.monic_prod_of_monic _ _ hm
  have hd : P.natDegree = ∑ j, m j := by
    simp only [P, Polynomial.natDegree_prod_of_monic _ _ hm,
      weierstrassPolynomial_natDegree]
  have hrepr (n : ℕ) (hn : P.natDegree = n) :
      weierstrassPolynomial (fun i : Fin n => P.coeff i) = P := by
    subst n
    exact weierstrassPolynomial_coeff_eq P hP
  exact hrepr _ hd

theorem analyticAt_weierstrassFamilyProductCoefficients
    {J : Type*} [Fintype J] (m : J → ℕ)
    (a : E → ∀ j, Fin (m j) → ℝ) (x : E)
    (ha : ∀ j, AnalyticAt ℝ (fun y => a y j) x) :
    AnalyticAt ℝ (weierstrassFamilyProductCoefficients m a) x := by
  apply analyticAt_pi_iff.mpr
  intro i
  exact analyticAt_polynomial_finset_prod_coeff Finset.univ
    (fun j y => weierstrassPolynomial (a y j)) x
    (fun j _ k => analyticAt_weierstrassPolynomial_coeff _ x (ha j) k) i

/-- Evaluating an analytic polynomial family along an analytic graph gives
an actual analytic test for membership in the zero set of that member. -/
theorem analyticAt_weierstrassPolynomial_eval_comp
    {m : ℕ} (a : E → Fin m → ℝ) (r : E → ℝ) (x : E)
    (ha : AnalyticAt ℝ a x) (hr : AnalyticAt ℝ r x) :
    AnalyticAt ℝ (fun y => (weierstrassPolynomial (a y)).eval (r y)) x := by
  simp only [weierstrassPolynomial_eval]
  apply (hr.pow m).add
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (analyticAt_pi_iff.mp ha i).mul (hr.pow (i : ℕ))

/-- An actual finite, disjoint analytic root stratification covering all
parameters of a finite analytic monic family, with no collision exclusion.
On each carrier the ordered root list is exactly the union of all member root
sets. Each member's value on each root graph is an analytic function on the
ambient open set; no constancy of its vanishing is asserted. Empty families and
degree-zero members are included. -/
theorem exists_analytic_polynomial_family_root_stratification
    [CompleteSpace E] {J : Type*} [Fintype J] (m : J → ℕ)
    (a : E → ∀ j, Fin (m j) → ℝ) (U : Set E) (hU : IsOpen U)
    (ha : ∀ j, AnalyticOnNhd ℝ (fun x => a x j) U) :
    ∃ T : AnalyticPolynomialRootStratification U
        (weierstrassFamilyProductCoefficients m a),
      (∀ i x, x ∈ (T.stratum i).carrier → ∀ t : ℝ,
        (∃ j, (weierstrassPolynomial (a x j)).eval t = 0) ↔
          ∃ k, t = T.roots i k x) ∧
      ∀ i (k : Fin (T.rootCount i)) j,
        AnalyticOnNhd ℝ
          (fun x => (weierstrassPolynomial (a x j)).eval (T.roots i k x))
          (T.stratum i).ambient := by
  classical
  have hprod : AnalyticOnNhd ℝ (weierstrassFamilyProductCoefficients m a) U :=
    fun x hx => analyticAt_weierstrassFamilyProductCoefficients m a x
      (fun j => ha j x hx)
  obtain ⟨T⟩ := exists_analytic_polynomial_root_stratification
    (weierstrassFamilyProductCoefficients m a) U hU hprod
  refine ⟨T, ?_, ?_⟩
  · intro i x hx t
    have h := T.original_roots_iff i x hx t
    rw [weierstrassPolynomial_familyProductCoefficients] at h
    simpa only [Polynomial.eval_prod, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] using h
  · intro i k j x hx
    exact analyticAt_weierstrassPolynomial_eval_comp _ _ x
      (ha j x (T.ambient_subset_domain i hx)) (T.roots_analytic i k x hx)

end PlanarNikodym
