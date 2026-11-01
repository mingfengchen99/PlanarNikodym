import PlanarNikodym.Geometry.AnalyticPolynomialRootBranches

/-! Joint continuity of actual polynomial derivative evaluation from the
original coefficient continuity. All expansions have a fixed finite length. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [TopologicalSpace E]

theorem continuousAt_weierstrassPolynomial_coeff {m : ℕ}
    (a : E → Fin m → ℝ) (x : E) (ha : ContinuousAt a x) (k : ℕ) :
    ContinuousAt (fun y => (weierstrassPolynomial (a y)).coeff k) x := by
  simp only [weierstrassPolynomial, coeff_add, finsetSum_coeff, coeff_C_mul]
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro i _
  exact ((continuous_apply i).continuousAt.comp ha).mul continuousAt_const

theorem continuousAt_joint_weierstrassPolynomial_iterate_derivative_eval
    {m : ℕ} (a : E → Fin m → ℝ) (x : E) (t : ℝ)
    (ha : ContinuousAt a x) (k : ℕ) :
    ContinuousAt (fun z : E × ℝ =>
      (derivative^[k] (weierstrassPolynomial (a z.1))).eval z.2) (x, t) := by
  have hd (y : E) : (derivative^[k] (weierstrassPolynomial (a y))).natDegree < m + 1 := by
    have h := natDegree_iterate_derivative (weierstrassPolynomial (a y)) k
    rw [weierstrassPolynomial_natDegree] at h
    omega
  have he (z : E × ℝ) :
      (derivative^[k] (weierstrassPolynomial (a z.1))).eval z.2 =
        ∑ i ∈ Finset.range (m + 1),
          (i + k).descFactorial k • (weierstrassPolynomial (a z.1)).coeff (i + k) * z.2 ^ i := by
    rw [eval_eq_sum_range' (hd z.1)]
    simp only [coeff_iterate_derivative]
  simp_rw [he]
  apply tendsto_finsetSum
  intro i _
  have hc : ContinuousAt (fun z : E × ℝ =>
      (weierstrassPolynomial (a z.1)).coeff (i + k)) (x, t) :=
    ContinuousAt.comp (f := fun z : E × ℝ => z.1)
      (g := fun y => (weierstrassPolynomial (a y)).coeff (i + k))
      (continuousAt_weierstrassPolynomial_coeff a x ha (i + k)) continuousAt_fst
  simp only [nsmul_eq_mul]
  change ContinuousAt (fun z : E × ℝ =>
    ((i + k).descFactorial k : ℝ) * (weierstrassPolynomial (a z.1)).coeff (i + k) *
      z.2 ^ i) (x, t)
  exact (continuousAt_const.mul hc).mul (continuousAt_snd.pow i)

end PlanarNikodym
