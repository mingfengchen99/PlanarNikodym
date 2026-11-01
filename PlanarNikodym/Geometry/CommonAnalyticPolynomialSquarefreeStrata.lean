import PlanarNikodym.Geometry.AnalyticPolynomialSquarefreeStrata
import PlanarNikodym.Geometry.CommonAnalyticPolynomialGcdTests

/-! Squarefree reduction with finite analytic branch tests on one original
domain, and actual quotient coefficients represented as analytic fractions. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weierstrassPolynomial_derivative_top_coeff {M : ℕ} (a : Fin M → ℝ) :
    (weierstrassPolynomial a).derivative.coeff (M - 1) = (M : ℝ) := by
  have hd : (weierstrassPolynomial a).derivative.natDegree = M - 1 := by
    rw [Polynomial.natDegree_derivative, weierstrassPolynomial_natDegree]
  rw [← hd, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_derivative,
    (weierstrassPolynomial_monic a).leadingCoeff, weierstrassPolynomial_natDegree, one_mul]

theorem analyticFractionOn_weierstrassDerivativeMonicCoefficients
    {U V : Set E} {M : ℕ} (a : E → Fin M → ℝ)
    (ha : ∀ i, AnalyticFractionOn U V (fun x => a x i))
    (i : Fin (M - 1)) :
    AnalyticFractionOn U V (fun x => weierstrassDerivativeMonicCoefficients a x i) := by
  have hM : M ≠ 0 := by have := i.isLt; omega
  change AnalyticFractionOn U V (fun x =>
    (weierstrassPolynomial (a x)).derivative.coeff i /
    (weierstrassPolynomial (a x)).derivative.coeff (M - 1))
  simp_rw [weierstrassPolynomial_derivative_top_coeff]
  simp only [Polynomial.coeff_derivative]
  exact ((analyticFractionOn_weierstrassPolynomial_coeff a ha (i + 1)).mul
    (AnalyticFractionOn.const U V _)).div (AnalyticFractionOn.const U V _)
    (fun _ _ => by exact_mod_cast hM)

structure CommonAnalyticPolynomialSquarefreeStratification
    {M : ℕ} (U V : Set E) (a : E → Fin M → ℝ)
    extends AnalyticPolynomialSquarefreeStratification V a where
  ambient_common : ∀ i, CommonAnalyticOpen U (stratum i).ambient
  coefficient_fraction : ∀ i k, AnalyticFractionOn U (stratum i).ambient
    (fun x => (stratum i).coefficients x k)
  zero_test_fraction : ∀ i k, AnalyticFractionOn U (stratum i).ambient
    (fun x => (stratum i).zeroTests x k)

theorem weierstrassPolynomial_of_monic_coefficients_degree
    (P : ℝ[X]) (hP : P.Monic) (n : ℕ) (hn : P.natDegree = n) :
    weierstrassPolynomial (fun i : Fin n => P.coeff i) = P := by
  subst n
  exact weierstrassPolynomial_coeff_eq P hP

/-- An all-parameter squarefree quotient tree with a common analytic domain;
no discriminant, constant multiplicity or chosen-gcd premise is assumed. -/
theorem exists_common_analytic_fraction_squarefree_stratification
    {M : ℕ} (a : E → Fin M → ℝ) (U V : Set E) (hU : IsOpen U)
    (hV : CommonAnalyticOpen U V)
    (ha : ∀ i, AnalyticFractionOn U V (fun x => a x i)) :
    Nonempty (CommonAnalyticPolynomialSquarefreeStratification U V a) := by
  classical
  have haA : AnalyticOnNhd ℝ a V := by
    intro x hx
    exact analyticAt_pi_iff.mpr (fun i => (ha i).analyticOnNhd (hV.isOpen hU) hV.subset x hx)
  let b := weierstrassDerivativeMonicCoefficients a
  obtain ⟨T⟩ := exists_common_analytic_fraction_gcd_stratification a b U V hU hV ha
    (analyticFractionOn_weierstrassDerivativeMonicCoefficients a ha)
  let G (i : T.Index) (x : E) := weierstrassPolynomial ((T.stratum i).coefficients x)
  let Q (i : T.Index) (x : E) := weierstrassPolynomial (a x) /ₘ G i x
  have hgdeg (i : T.Index) : (T.stratum i).degree ≤ M := by
    have h := T.degree_le_right i (0 : E)
    rw [weierstrassPolynomial_natDegree] at h
    exact h.trans (Nat.sub_le _ _)
  have hqdegree (i : T.Index) (x : E) :
      (Q i x).natDegree = M - (T.stratum i).degree := by
    rw [Polynomial.natDegree_divByMonic _ (weierstrassPolynomial_monic _),
      weierstrassPolynomial_natDegree, weierstrassPolynomial_natDegree]
  have hqmonic (i : T.Index) (x : E) : (Q i x).Monic := by
    change (Q i x).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_divByMonic_of_monic (weierstrassPolynomial_monic _),
      (weierstrassPolynomial_monic (a x)).leadingCoeff]
    rw [Polynomial.degree_eq_natDegree (weierstrassPolynomial_monic _).ne_zero,
      Polynomial.degree_eq_natDegree (weierstrassPolynomial_monic _).ne_zero,
      weierstrassPolynomial_natDegree, weierstrassPolynomial_natDegree]
    exact_mod_cast hgdeg i
  let c (i : T.Index) : E → Fin (M - (T.stratum i).degree) → ℝ :=
    fun x j => (Q i x).coeff j
  have hc_eq (i : T.Index) (x : E) : weierstrassPolynomial (c i x) = Q i x := by
    exact weierstrassPolynomial_of_monic_coefficients_degree (Q i x) (hqmonic i x)
      (M - (T.stratum i).degree) (hqdegree i x)
  have hqactual (i : T.Index) (x : E) (hx : x ∈ (T.stratum i).carrier) :
      Q i x = polynomialDerivativeQuotient (weierstrassPolynomial (a x)) := by
    have hspec (D : ℝ[X]) : D ∣ G i x ↔
        D ∣ weierstrassPolynomial (a x) ∧ D ∣ (weierstrassPolynomial (a x)).derivative :=
      ((T.valid i).2.2.2.2.2 x hx D).trans
        (weierstrass_derivative_normalization_common_divisors a x D)
    have hdiv := (hspec (G i x)).mp dvd_rfl
    have he := polynomialDerivativeGcd_eq_of_monic_gcd
      (weierstrassPolynomial (a x)) (G i x) (weierstrassPolynomial_monic _).ne_zero
      (weierstrassPolynomial_monic _) hdiv.1 hdiv.2
      (fun D hD hD' => (hspec D).mpr ⟨hD, hD'⟩)
    change weierstrassPolynomial (a x) /ₘ G i x = _
    rw [Polynomial.divByMonic_eq_div _ (weierstrassPolynomial_monic _)]
    change weierstrassPolynomial (a x) / G i x = _
    rw [he]
    rfl
  let S (i : T.Index) : AnalyticPolynomialGcdStratumData E :=
    { T.stratum i with degree := M - (T.stratum i).degree, coefficients := c i }
  refine ⟨{
    Index := T.Index
    indexFintype := T.indexFintype
    stratum := S
    ambient_open := fun i => (T.valid i).1
    carrier_subset_ambient := fun i => (T.valid i).2.1
    ambient_subset_domain := T.ambient_subset_domain
    coefficients_analytic := ?_
    tests_analytic := fun i => (T.valid i).2.2.2.1
    carrier_eq_tests := fun i => (T.valid i).2.2.2.2.1
    degree_le := fun i => Nat.sub_le _ _
    disjoint := T.disjoint
    cover := T.cover
    quotient_eq := ?_
    collision_ne_zero := ?_
    roots_iff := ?_
    ambient_common := T.ambient_common
    coefficient_fraction := ?_
    zero_test_fraction := T.zero_test_fraction }⟩
  · intro i x hx
    apply analyticAt_pi_iff.mpr
    intro j
    exact (analyticAt_polynomial_monic_division_coeff
      (fun y => weierstrassPolynomial (a y)) (T.stratum i).coefficients x (M + 1)
      (analyticAt_weierstrassPolynomial_coeff a x (haA x (T.ambient_subset_domain i hx)))
      (fun y k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [weierstrassPolynomial_natDegree]; omega))
      ((T.valid i).2.2.1 x hx) j).1
  · intro i x hx
    exact (hc_eq i x).trans (hqactual i x hx)
  · intro i x hx
    apply weierstrassCollisionDet_ne_zero_of_separable
    rw [hc_eq, hqactual i x hx]
    exact polynomialDerivativeQuotient_separable _ (weierstrassPolynomial_monic _).ne_zero
  · intro i x hx t
    rw [hc_eq, hqactual i x hx]
    exact polynomialDerivativeQuotient_eval_eq_zero_iff _ (weierstrassPolynomial_monic _).ne_zero t

  · intro i j
    exact (analyticFractionOn_polynomial_monic_division_coeff
      (fun y => weierstrassPolynomial (a y)) (T.stratum i).coefficients U
      (T.stratum i).ambient (M + 1)
      (fun k => (analyticFractionOn_weierstrassPolynomial_coeff a ha k).mono
        (T.ambient_subset_domain i))
      (fun y k hk => Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [weierstrassPolynomial_natDegree]; omega))
      (T.coefficient_fraction i) j).1

end PlanarNikodym
