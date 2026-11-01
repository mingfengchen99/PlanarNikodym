import PlanarNikodym.Geometry.AnalyticFractions
import PlanarNikodym.Geometry.AnalyticPolynomialDegreeStrata

/-! Actual monic Euclidean division preserves analytic fractions whose
numerators and denominators are analytic on one common original domain. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticFractionOn_polynomial_monic_division_coeff
    (p : E → ℝ[X]) {m : ℕ} (a : E → Fin m → ℝ) (U V : Set E) (N : ℕ)
    (hp : ∀ k, AnalyticFractionOn U V (fun x => (p x).coeff k))
    (hbound : ∀ x k, N ≤ k → (p x).coeff k = 0)
    (ha : ∀ i, AnalyticFractionOn U V (fun x => a x i)) (k : ℕ) :
    AnalyticFractionOn U V (fun x => (p x /ₘ weierstrassPolynomial (a x)).coeff k) ∧
    AnalyticFractionOn U V (fun x => (p x %ₘ weierstrassPolynomial (a x)).coeff k) := by
  classical
  let A := analyticFractionFunctionSubring U V
  let b : ℕ → A := fun i => ⟨fun x => (p x).coeff i, hp i⟩
  let c : Fin m → A := fun i => ⟨fun x => a x i, ha i⟩
  let P : A[X] := ∑ i ∈ Finset.range N, monomial i (b i)
  let Q : A[X] := X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ)
  have hQ : Q.Monic := by
    apply (monic_X_pow m).add_of_left
    simpa only [degree_X_pow] using degree_sum_fin_lt c
  have hPmap (x : E) : P.map (analyticFractionFunctionEval U V x) = p x := by
    ext i
    simp only [P, Polynomial.map_sum, Polynomial.map_monomial,
      analyticFractionFunctionEval_apply, b, finsetSum_coeff, coeff_monomial]
    by_cases hi : i < N
    · simp [hi]
    · simp [hi, hbound x i (Nat.le_of_not_gt hi)]
  have hQmap (x : E) : Q.map (analyticFractionFunctionEval U V x) =
      weierstrassPolynomial (a x) := by
    simp only [Q, weierstrassPolynomial, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      analyticFractionFunctionEval_apply, c]
  have hdiv (x : E) : (p x /ₘ weierstrassPolynomial (a x)).coeff k =
      ((P /ₘ Q).coeff k).val x := by
    rw [← hPmap x, ← hQmap x, ← Polynomial.map_divByMonic _ hQ, Polynomial.coeff_map]
    rfl
  have hmod (x : E) : (p x %ₘ weierstrassPolynomial (a x)).coeff k =
      ((P %ₘ Q).coeff k).val x := by
    rw [← hPmap x, ← hQmap x, ← Polynomial.map_modByMonic _ hQ, Polynomial.coeff_map]
    rfl
  constructor
  · simp_rw [hdiv]
    exact ((P /ₘ Q).coeff k).property
  · simp_rw [hmod]
    exact ((P %ₘ Q).coeff k).property


theorem analyticFractionOn_weierstrassPolynomial_coeff
    {U V : Set E} {m : ℕ} (a : E → Fin m → ℝ)
    (ha : ∀ i, AnalyticFractionOn U V (fun x => a x i)) (k : ℕ) :
    AnalyticFractionOn U V (fun x => (weierstrassPolynomial (a x)).coeff k) := by
  classical
  simp only [weierstrassPolynomial, coeff_add, finsetSum_coeff, coeff_C_mul]
  exact (AnalyticFractionOn.const U V _).add
    (AnalyticFractionOn.finset_sum Finset.univ _ (fun i _ =>
      (ha i).mul (AnalyticFractionOn.const U V _)))

/-- The actual normalized remainder coefficients are fractions on the
nonzero-leading-coefficient branch, all on the same original domain. -/
theorem analyticFractionOn_polynomialMonicCoefficients
    {U V : Set E} (r : E → ℝ[X]) (d : ℕ)
    (hr : ∀ k, AnalyticFractionOn U V (fun x => (r x).coeff k))
    (i : Fin d) :
    AnalyticFractionOn U (V ∩ {x | (r x).coeff d ≠ 0})
      (fun x => polynomialMonicCoefficients r d x i) := by
  exact ((hr i).mono inter_subset_left).div ((hr d).mono inter_subset_left)
    (fun _ hx => hx.2)

end PlanarNikodym
