import PlanarNikodym.Tame.DefinablePolynomialRootLists
import PlanarNikodym.Geometry.AnalyticGlobalPolynomialRoots

/-! Definability of the actual root-count domains and of their constructed
analytic root branches. All graphs are obtained from real field formulas. -/
noncomputable section
open Set Polynomial
namespace PlanarNikodym

theorem ranDefinableOn_weierstrassPolynomial_coeff {ι : Type*}
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ i, RanDefinableOn (fun x => a x i) S) (k : ℕ) :
    RanDefinableOn (fun x => (weierstrassPolynomial (a x)).coeff k) S := by
  by_cases hk : k < m
  · apply (ha ⟨k, hk⟩).congr
    intro x _
    exact (weierstrassPolynomial_coeff_lt (a x) ⟨k, hk⟩).symm
  · by_cases he : k = m
    · subst k
      have hcoeff (x : ι → ℝ) : (weierstrassPolynomial (a x)).coeff m = 1 := by
        simpa only [weierstrassPolynomial_natDegree] using
          (weierstrassPolynomial_monic (a x)).coeff_natDegree
      simp_rw [hcoeff]
      exact (ranDefinableFun_const 1).ranDefinableOn hS
    · have hcoeff (x : ι → ℝ) : (weierstrassPolynomial (a x)).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [weierstrassPolynomial_natDegree]; omega)
      simp_rw [hcoeff]
      exact (ranDefinableFun_const 0).ranDefinableOn hS

theorem ranDefinableOn_polynomial_resultant {ι : Type*} [Finite ι]
    {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (f g : (ι → ℝ) → ℝ[X]) (m n : ℕ)
    (hf : ∀ k, RanDefinableOn (fun x => (f x).coeff k) S)
    (hg : ∀ k, RanDefinableOn (fun x => (g x).coeff k) S) :
    RanDefinableOn (fun x => (f x).resultant (g x) m n) S := by
  unfold Polynomial.resultant
  apply ranDefinableOn_det hS
  intro i j
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · exact (ranDefinableFun_const 0).ranDefinableOn hS
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · exact (ranDefinableFun_const 0).ranDefinableOn hS

theorem ranDefinableOn_weierstrassCollisionDet {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ i, RanDefinableOn (fun x => a x i) S) :
    RanDefinableOn (fun x => weierstrassCollisionDet (a x)) S := by
  apply ranDefinableOn_polynomial_resultant hS
  · exact ranDefinableOn_weierstrassPolynomial_coeff hS ha
  · intro k
    simp only [Polynomial.coeff_derivative]
    exact (ranDefinableOn_weierstrassPolynomial_coeff hS ha (k + 1)).mul
      ((ranDefinableFun_const _).ranDefinableOn hS) hS

theorem ranDefinable_polynomialRealRootCount {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ i, RanDefinableOn (fun x => a x i) S) (n : ℕ) :
    RanDefinable {x | x ∈ S ∧ polynomialRealRootCount (a x) = n} := by
  simpa only [polynomialRealRootCount_eq_iff_exists_ordered_roots,
    IsOrderedPolynomialRootList] using
    ranDefinable_exists_orderedPolynomialRootList hS ha n

theorem ranDefinable_polynomialSimpleRootCountDomain {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ i, RanDefinableOn (fun x => a x i) S) (n : ℕ) :
    RanDefinable (polynomialSimpleRootCountDomain a S n) := by
  convert ((ranDefinableOn_weierstrassCollisionDet hS ha).nonzeroSet hS).inter
    (ranDefinable_polynomialRealRootCount hS ha n) using 1
  ext x
  simp only [polynomialSimpleRootCountDomain, mem_inter_iff, mem_setOf_eq]
  tauto

theorem ranDefinableOn_orderedPolynomialRealRoot {ι : Type*} [Finite ι]
    {m : ℕ} {a : (ι → ℝ) → Fin m → ℝ} {S : Set (ι → ℝ)}
    (hS : RanDefinable S) (ha : ∀ i, RanDefinableOn (fun x => a x i) S)
    (n : ℕ) (i : Fin n) :
    RanDefinableOn (fun x => orderedPolynomialRealRoot (a x) n i)
      (polynomialSimpleRootCountDomain a S n) := by
  have hD := ranDefinable_polynomialSimpleRootCountDomain hS ha n
  exact ranDefinableOn_orderedPolynomialRootBranch hD
    (fun j => (ha j).restrict hD (fun _ hx => hx.1))
    (fun x => orderedPolynomialRealRoot (a x) n)
    (fun x hx => orderedPolynomialRealRoot_spec (a x) n hx.2.2) i

/-- Original definable analytic coefficients suffice for both the analytic and
definable graphs of all ordered roots on each actual simple root-count domain. -/
theorem exists_global_ordered_analytic_definable_polynomial_roots
    {ι : Type*} [Fintype ι] {m : ℕ} (a : (ι → ℝ) → Fin m → ℝ)
    (V : Set (ι → ℝ)) (hV : IsOpen V) (hdV : RanDefinable V)
    (ha : AnalyticOnNhd ℝ a V)
    (hda : ∀ i, RanDefinableOn (fun x => a x i) V) (n : ℕ) :
    IsOpen (polynomialSimpleRootCountDomain a V n) ∧
    RanDefinable (polynomialSimpleRootCountDomain a V n) ∧
    ∃ ρ : Fin n → (ι → ℝ) → ℝ,
      (∀ i, AnalyticOnNhd ℝ (ρ i) (polynomialSimpleRootCountDomain a V n)) ∧
      (∀ i, RanDefinableOn (ρ i) (polynomialSimpleRootCountDomain a V n)) ∧
      (∀ x ∈ polynomialSimpleRootCountDomain a V n, StrictMono (fun i => ρ i x)) ∧
      ∀ x ∈ polynomialSimpleRootCountDomain a V n, ∀ t,
        (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = ρ i x := by
  refine ⟨isOpen_polynomialSimpleRootCountDomain a V hV ha n,
    ranDefinable_polynomialSimpleRootCountDomain hdV hda n,
    (fun i x => orderedPolynomialRealRoot (a x) n i),
    analyticOnNhd_orderedPolynomialRealRoot a V hV ha n,
    ranDefinableOn_orderedPolynomialRealRoot hdV hda n, ?_, ?_⟩
  · intro x hx
    exact (orderedPolynomialRealRoot_spec (a x) n hx.2.2).1
  · intro x hx
    exact (orderedPolynomialRealRoot_spec (a x) n hx.2.2).2

end PlanarNikodym
