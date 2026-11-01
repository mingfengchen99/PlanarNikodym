import PlanarNikodym.Geometry.AnalyticFractionPolynomialDivision
import PlanarNikodym.Geometry.WeierstrassDiscriminant

/-! Sylvester determinants of actual analytic fractions remain analytic
fractions on the same original domain, with no nonvanishing premise. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AnalyticFractionOn.finset_prod {U V : Set E} {ι : Type*} (s : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ s, AnalyticFractionOn U V (f i)) :
    AnalyticFractionOn U V (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AnalyticFractionOn.const U V 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem analyticFractionOn_det {U V : Set E} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : E → Matrix ι ι ℝ)
    (hA : ∀ i j, AnalyticFractionOn U V (fun x => A x i j)) :
    AnalyticFractionOn U V (fun x => (A x).det) := by
  simp only [Matrix.det_apply']
  exact AnalyticFractionOn.finset_sum Finset.univ _ (fun σ _ =>
    (AnalyticFractionOn.const U V _).mul
      (AnalyticFractionOn.finset_prod Finset.univ _ (fun i _ => hA (σ i) i)))

theorem analyticFractionOn_polynomial_resultant
    {U V : Set E} (f g : E → ℝ[X]) (m n : ℕ)
    (hf : ∀ k, AnalyticFractionOn U V (fun x => (f x).coeff k))
    (hg : ∀ k, AnalyticFractionOn U V (fun x => (g x).coeff k)) :
    AnalyticFractionOn U V (fun x => (f x).resultant (g x) m n) := by
  unfold Polynomial.resultant
  apply analyticFractionOn_det
  intro i j
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · exact AnalyticFractionOn.const U V _
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · exact AnalyticFractionOn.const U V _

theorem analyticFractionOn_weierstrassCollisionDet
    {U V : Set E} {m : ℕ} (a : E → Fin m → ℝ)
    (ha : ∀ i, AnalyticFractionOn U V (fun x => a x i)) :
    AnalyticFractionOn U V (fun x => weierstrassCollisionDet (a x)) := by
  apply analyticFractionOn_polynomial_resultant
  · exact analyticFractionOn_weierstrassPolynomial_coeff a ha
  · intro k
    simp only [Polynomial.coeff_derivative]
    exact (analyticFractionOn_weierstrassPolynomial_coeff a ha (k + 1)).mul
      (AnalyticFractionOn.const U V _)

end PlanarNikodym
