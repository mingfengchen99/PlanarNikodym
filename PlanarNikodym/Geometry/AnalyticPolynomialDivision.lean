import PlanarNikodym.Geometry.AnalyticPolynomialRootBranches
import Mathlib.Algebra.Polynomial.Div

/-! Actual monic polynomial division preserves analytic coefficient dependence.
The proof performs division in the ring of functions analytic at the base point,
then specializes by evaluation. No analytic quotient is postulated. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Global real functions whose germs at the chosen point are analytic. -/
def analyticAtFunctionSubring (x₀ : E) : Subring (E → ℝ) where
  carrier := {f | AnalyticAt ℝ f x₀}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

/-- Evaluate an actual analytic coefficient function at any parameter. -/
def analyticAtFunctionEval (x₀ x : E) : analyticAtFunctionSubring x₀ →+* ℝ :=
  (Pi.evalRingHom (fun _ : E => ℝ) x).comp (analyticAtFunctionSubring x₀).subtype

@[simp] theorem analyticAtFunctionEval_apply (x₀ x : E)
    (f : analyticAtFunctionSubring x₀) : analyticAtFunctionEval x₀ x f = f.val x := rfl

/-- Quotient and remainder of the actual monic division have analytic coefficients.
The numerator has a common finite support bound; the denominator is the original
fixed-degree monic coefficient family, including degree zero. -/
theorem analyticAt_polynomial_monic_division_coeff
    (p : E → ℝ[X]) {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (N : ℕ)
    (hp : ∀ k, AnalyticAt ℝ (fun x => (p x).coeff k) x₀)
    (hbound : ∀ x k, N ≤ k → (p x).coeff k = 0)
    (ha : AnalyticAt ℝ a x₀) (k : ℕ) :
    AnalyticAt ℝ (fun x => (p x /ₘ weierstrassPolynomial (a x)).coeff k) x₀ ∧
    AnalyticAt ℝ (fun x => (p x %ₘ weierstrassPolynomial (a x)).coeff k) x₀ := by
  classical
  let A := analyticAtFunctionSubring x₀
  let b : ℕ → A := fun i => ⟨fun x => (p x).coeff i, hp i⟩
  let c : Fin m → A := fun i => ⟨fun x => a x i, analyticAt_pi_iff.mp ha i⟩
  let P : A[X] := ∑ i ∈ Finset.range N, monomial i (b i)
  let Q : A[X] := X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ)
  have hQ : Q.Monic := by
    apply (monic_X_pow m).add_of_left
    simpa only [degree_X_pow] using degree_sum_fin_lt c
  have hPmap (x : E) : P.map (analyticAtFunctionEval x₀ x) = p x := by
    ext i
    simp only [P, Polynomial.map_sum, Polynomial.map_monomial,
      analyticAtFunctionEval_apply, b, finsetSum_coeff, coeff_monomial]
    by_cases hi : i < N
    · simp [hi]
    · simp [hi, hbound x i (Nat.le_of_not_gt hi)]
  have hQmap (x : E) : Q.map (analyticAtFunctionEval x₀ x) =
      weierstrassPolynomial (a x) := by
    simp only [Q, weierstrassPolynomial, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      analyticAtFunctionEval_apply, c]
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

end PlanarNikodym
