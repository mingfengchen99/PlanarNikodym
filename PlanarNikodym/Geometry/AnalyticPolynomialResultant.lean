import PlanarNikodym.Rank.AnalyticCoefficients
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Fixed-size Sylvester determinants of analytic coefficient families.
The matrix and its Bezout identity are the actual Mathlib constructions.
The size is fixed independently of the parameter, so coefficient degree drops
do not introduce a discontinuous choice of matrix dimensions. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology

namespace PlanarNikodym

/-- The actual Sylvester determinant is analytic when its finitely many
entries are analytic coefficient functions. -/
theorem analyticAt_polynomial_resultant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ[X]) (m n : ℕ) (x : E)
    (hf : ∀ k, AnalyticAt ℝ (fun y => (f y).coeff k) x)
    (hg : ∀ k, AnalyticAt ℝ (fun y => (g y).coeff k) x) :
    AnalyticAt ℝ (fun y => (f y).resultant (g y) m n) x := by
  unfold Polynomial.resultant
  apply analyticAt_det
  intro i j
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · exact analyticAt_const
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · exact analyticAt_const

/-- Common roots annihilate the actual fixed-size resultant, by evaluating its
Bezout identity. The nonempty size assumption is necessary: the determinant
of a zero-by-zero Sylvester matrix is one even for two zero polynomials. -/
theorem polynomial_resultant_eq_zero_of_common_root
    (f g : ℝ[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0)
    (t : ℝ) (hft : f.eval t = 0) (hgt : g.eval t = 0) :
    f.resultant g m n = 0 := by
  obtain ⟨a, b, _, _, heq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  have h := congrArg (fun P : ℝ[X] => P.eval t) heq
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    hft, hgt, zero_mul, zero_add] using h.symm

/-- Nonvanishing of the Sylvester determinant rules out every common real root. -/
theorem polynomial_no_common_root_of_resultant_ne_zero
    (f g : ℝ[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0)
    (hres : f.resultant g m n ≠ 0) :
    ∀ t : ℝ, ¬ (f.eval t = 0 ∧ g.eval t = 0) := by
  rintro t ⟨hft, hgt⟩
  exact hres (polynomial_resultant_eq_zero_of_common_root f g m n hf hg hmn t hft hgt)

end PlanarNikodym
