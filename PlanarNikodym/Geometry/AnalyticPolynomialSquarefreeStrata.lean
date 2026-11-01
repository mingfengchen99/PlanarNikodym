import PlanarNikodym.Geometry.AnalyticPolynomialGcdStrata

/-! Finite analytic squarefree reductions for arbitrary monic analytic families.
Repeated roots and degree jumps of the derivative gcd are retained in finitely
many actual analytic-equation strata. The quotient coefficients extend
analytically to open ambient sets, with a fixed monic degree on each ambient. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weierstrassDerivativeMonicCoefficients {M : ℕ} (a : E → Fin M → ℝ) :
    E → Fin (M - 1) → ℝ :=
  polynomialMonicCoefficients (fun x => (weierstrassPolynomial (a x)).derivative) (M - 1)

private theorem weierstrass_derivative_top_coeff {M : ℕ} (a : Fin M → ℝ) :
    (weierstrassPolynomial a).derivative.coeff (M - 1) = (M : ℝ) := by
  have hd : (weierstrassPolynomial a).derivative.natDegree = M - 1 := by
    rw [Polynomial.natDegree_derivative, weierstrassPolynomial_natDegree]
  rw [← hd, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_derivative,
    (weierstrassPolynomial_monic a).leadingCoeff, weierstrassPolynomial_natDegree, one_mul]

theorem analyticAt_weierstrassDerivativeMonicCoefficients
    {M : ℕ} (a : E → Fin M → ℝ) (x : E) (ha : AnalyticAt ℝ a x) :
    AnalyticAt ℝ (weierstrassDerivativeMonicCoefficients a) x := by
  by_cases hM : M = 0
  · subst M
    apply analyticAt_pi_iff.mpr
    intro i
    exact Fin.elim0 i
  · apply analyticAt_polynomialMonicCoefficients
    · intro k
      simp only [Polynomial.coeff_derivative]
      exact (analyticAt_weierstrassPolynomial_coeff a x ha (k + 1)).mul analyticAt_const
    · rw [weierstrass_derivative_top_coeff]
      exact_mod_cast hM

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Derivative normalization retains exactly the common divisors with the
original monic polynomial, including the constant polynomial case. -/
theorem weierstrass_derivative_normalization_common_divisors
    {M : ℕ} (a : E → Fin M → ℝ) (x : E) (D : ℝ[X]) :
    (D ∣ weierstrassPolynomial (a x) ∧
      D ∣ weierstrassPolynomial (weierstrassDerivativeMonicCoefficients a x)) ↔
    (D ∣ weierstrassPolynomial (a x) ∧ D ∣ (weierstrassPolynomial (a x)).derivative) := by
  by_cases hM : M = 0
  · subst M
    simp [weierstrassPolynomial]
  · apply and_congr_right
    intro _
    apply polynomial_monic_normalization_divisors_iff
    refine ⟨?_, ?_⟩
    · rw [weierstrass_derivative_top_coeff]
      exact_mod_cast hM
    · intro k hk
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa only [Polynomial.natDegree_derivative, weierstrassPolynomial_natDegree] using hk

/-- An actual finite squarefree coefficient cover. Each piece is given by
finitely many analytic equations inside an open ambient subset of the domain.
The reduced monic polynomial is the literal derivative-gcd quotient on the
piece and has the complete original real zero set there. -/
structure AnalyticPolynomialSquarefreeStratification
    {M : ℕ} (U : Set E) (a : E → Fin M → ℝ) where
  Index : Type
  indexFintype : Fintype Index
  stratum : Index → AnalyticPolynomialGcdStratumData E
  ambient_open : ∀ i, IsOpen (stratum i).ambient
  carrier_subset_ambient : ∀ i, (stratum i).carrier ⊆ (stratum i).ambient
  ambient_subset_domain : ∀ i, (stratum i).ambient ⊆ U
  coefficients_analytic : ∀ i, AnalyticOnNhd ℝ (stratum i).coefficients (stratum i).ambient
  tests_analytic : ∀ i, AnalyticOnNhd ℝ (stratum i).zeroTests (stratum i).ambient
  carrier_eq_tests : ∀ i x, x ∈ (stratum i).carrier ↔
    x ∈ (stratum i).ambient ∧ ∀ j, (stratum i).zeroTests x j = 0
  degree_le : ∀ i, (stratum i).degree ≤ M
  disjoint : Pairwise (fun i j => Disjoint (stratum i).carrier (stratum j).carrier)
  cover : ∀ x, x ∈ U ↔ ∃ i, x ∈ (stratum i).carrier
  quotient_eq : ∀ i x, x ∈ (stratum i).carrier →
    weierstrassPolynomial ((stratum i).coefficients x) =
      polynomialDerivativeQuotient (weierstrassPolynomial (a x))
  collision_ne_zero : ∀ i x, x ∈ (stratum i).carrier →
    weierstrassCollisionDet ((stratum i).coefficients x) ≠ 0
  roots_iff : ∀ i x, x ∈ (stratum i).carrier → ∀ t : ℝ,
    (weierstrassPolynomial ((stratum i).coefficients x)).eval t = 0 ↔
      (weierstrassPolynomial (a x)).eval t = 0

private theorem monic_coefficient_representation_of_degree
    (P : ℝ[X]) (hP : P.Monic) (n : ℕ) (hn : P.natDegree = n) :
    weierstrassPolynomial (fun i : Fin n => P.coeff i) = P := by
  subst n
  exact weierstrassPolynomial_coeff_eq P hP

/-- Arbitrary analytic monic families admit a finite disjoint analytic-equation
stratification with actual squarefree reductions. No original discriminant,
constant-rank, simple-root or preselected gcd hypothesis is required. -/
theorem exists_analytic_polynomial_squarefree_stratification
    {M : ℕ} (a : E → Fin M → ℝ) (U : Set E) (hU : IsOpen U)
    (ha : AnalyticOnNhd ℝ a U) :
    Nonempty (AnalyticPolynomialSquarefreeStratification U a) := by
  classical
  let b := weierstrassDerivativeMonicCoefficients a
  obtain ⟨T⟩ := exists_analytic_polynomial_gcd_stratification a b U hU ha
    (fun x hx => analyticAt_weierstrassDerivativeMonicCoefficients a x (ha x hx))
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
    exact monic_coefficient_representation_of_degree (Q i x) (hqmonic i x)
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
    roots_iff := ?_ }⟩
  · intro i x hx
    apply analyticAt_pi_iff.mpr
    intro j
    exact (analyticAt_polynomial_monic_division_coeff
      (fun y => weierstrassPolynomial (a y)) (T.stratum i).coefficients x (M + 1)
      (analyticAt_weierstrassPolynomial_coeff a x (ha x (T.ambient_subset_domain i hx)))
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

end PlanarNikodym
