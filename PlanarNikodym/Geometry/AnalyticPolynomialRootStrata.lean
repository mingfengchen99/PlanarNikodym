import PlanarNikodym.Geometry.AnalyticPolynomialSquarefreeStrata
import PlanarNikodym.Geometry.AnalyticGlobalPolynomialRoots

/-! Finite analytic root strata covering all parameters of a monic analytic
polynomial family, including repeated-root parameters. The base pieces are
finite analytic zero tests in open ambient sets. Each ambient has a fixed
number of globally ordered analytic roots of the actual squarefree reduction.
No connectedness or cell decomposition of the base pieces is asserted. -/

noncomputable section
open Set Filter Polynomial
open scoped Topology

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

structure AnalyticPolynomialRootStratification
    {M : ℕ} (U : Set E) (a : E → Fin M → ℝ) where
  Index : Type
  indexFintype : Fintype Index
  stratum : Index → AnalyticPolynomialGcdStratumData E
  rootCount : Index → ℕ
  roots : (i : Index) → Fin (rootCount i) → E → ℝ
  ambient_open : ∀ i, IsOpen (stratum i).ambient
  carrier_subset_ambient : ∀ i, (stratum i).carrier ⊆ (stratum i).ambient
  ambient_subset_domain : ∀ i, (stratum i).ambient ⊆ U
  coefficients_analytic : ∀ i, AnalyticOnNhd ℝ (stratum i).coefficients (stratum i).ambient
  tests_analytic : ∀ i, AnalyticOnNhd ℝ (stratum i).zeroTests (stratum i).ambient
  carrier_eq_tests : ∀ i x, x ∈ (stratum i).carrier ↔
    x ∈ (stratum i).ambient ∧ ∀ j, (stratum i).zeroTests x j = 0
  degree_le : ∀ i, (stratum i).degree ≤ M
  rootCount_le_degree : ∀ i, rootCount i ≤ (stratum i).degree
  disjoint : Pairwise (fun i j => Disjoint (stratum i).carrier (stratum j).carrier)
  cover : ∀ x, x ∈ U ↔ ∃ i, x ∈ (stratum i).carrier
  quotient_eq : ∀ i x, x ∈ (stratum i).carrier →
    weierstrassPolynomial ((stratum i).coefficients x) =
      polynomialDerivativeQuotient (weierstrassPolynomial (a x))
  collision_ne_zero : ∀ i x, x ∈ (stratum i).ambient →
    weierstrassCollisionDet ((stratum i).coefficients x) ≠ 0
  roots_analytic : ∀ i j, AnalyticOnNhd ℝ (roots i j) (stratum i).ambient
  roots_ordered : ∀ i x, x ∈ (stratum i).ambient → StrictMono (fun j => roots i j x)
  reduced_roots_iff : ∀ i x, x ∈ (stratum i).ambient → ∀ t : ℝ,
    (weierstrassPolynomial ((stratum i).coefficients x)).eval t = 0 ↔
      ∃ j, t = roots i j x
  original_roots_iff : ∀ i x, x ∈ (stratum i).carrier → ∀ t : ℝ,
    (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ j, t = roots i j x

/-- A genuine finite analytic root stratification for every analytic monic
family, with no discriminant, gcd, constant-rank, root-list or root-cover input.
Every original parameter, including every collision parameter, is covered. -/
theorem exists_analytic_polynomial_root_stratification
    {M : ℕ} (a : E → Fin M → ℝ) (U : Set E) (hU : IsOpen U)
    (ha : AnalyticOnNhd ℝ a U) :
    Nonempty (AnalyticPolynomialRootStratification U a) := by
  classical
  obtain ⟨T⟩ := exists_analytic_polynomial_squarefree_stratification a U hU ha
  letI : Fintype T.Index := T.indexFintype
  let I := Σ i : T.Index, Fin ((T.stratum i).degree + 1)
  let Ω (i : T.Index) (n : Fin ((T.stratum i).degree + 1)) : Set E :=
    polynomialSimpleRootCountDomain (T.stratum i).coefficients (T.stratum i).ambient n
  have hglobal (i : T.Index) (n : Fin ((T.stratum i).degree + 1)) :=
    exists_global_ordered_analytic_polynomial_roots
      (T.stratum i).coefficients (T.stratum i).ambient
      (T.ambient_open i) (T.coefficients_analytic i) n
  let ρ (i : T.Index) (n : Fin ((T.stratum i).degree + 1)) : Fin n → E → ℝ :=
    Classical.choose (hglobal i n).2
  have hρ (i : T.Index) (n : Fin ((T.stratum i).degree + 1)) :=
    Classical.choose_spec (hglobal i n).2
  let S (i : I) : AnalyticPolynomialGcdStratumData E :=
    { T.stratum i.1 with
      carrier := (T.stratum i.1).carrier ∩ Ω i.1 i.2
      ambient := Ω i.1 i.2 }
  refine ⟨{
    Index := I
    indexFintype := inferInstance
    stratum := S
    rootCount := fun i => i.2
    roots := fun i => ρ i.1 i.2
    ambient_open := fun i => (hglobal i.1 i.2).1
    carrier_subset_ambient := fun _ _ hx => hx.2
    ambient_subset_domain := fun i x hx => T.ambient_subset_domain i.1 hx.1
    coefficients_analytic := fun i x hx => T.coefficients_analytic i.1 x hx.1
    tests_analytic := fun i x hx => T.tests_analytic i.1 x hx.1
    carrier_eq_tests := ?_
    degree_le := fun i => T.degree_le i.1
    rootCount_le_degree := fun i => Nat.le_of_lt_succ i.2.isLt
    disjoint := ?_
    cover := ?_
    quotient_eq := fun i x hx => T.quotient_eq i.1 x hx.1
    collision_ne_zero := fun _ _ hx => hx.2.1
    roots_analytic := fun i => (hρ i.1 i.2).1
    roots_ordered := fun i => (hρ i.1 i.2).2.1
    reduced_roots_iff := fun i => (hρ i.1 i.2).2.2
    original_roots_iff := ?_ }⟩
  · intro i x
    constructor
    · rintro ⟨hc, hΩ⟩
      exact ⟨hΩ, ((T.carrier_eq_tests i.1 x).mp hc).2⟩
    · rintro ⟨hΩ, ht⟩
      exact ⟨(T.carrier_eq_tests i.1 x).mpr ⟨hΩ.1, ht⟩, hΩ⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    rcases i with ⟨i, n⟩
    rcases j with ⟨j, m⟩
    by_cases he : i = j
    · subst j
      have hnm : n ≠ m := fun h => hij (by cases h; rfl)
      exact Set.disjoint_left.mp
        ((polynomialSimpleRootCountDomain_finite_partition
          (T.stratum i).coefficients (T.stratum i).ambient).2 hnm) hi.2 hj.2
    · exact Set.disjoint_left.mp (T.disjoint he) hi.1 hj.1
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (T.cover x).mp hx
      let n : Fin ((T.stratum i).degree + 1) :=
        ⟨polynomialRealRootCount ((T.stratum i).coefficients x),
          Nat.lt_succ_of_le (polynomialRealRootCount_le _)⟩
      refine ⟨⟨i, n⟩, hi, ?_⟩
      exact ⟨T.carrier_subset_ambient i hi, T.collision_ne_zero i x hi, rfl⟩
    · rintro ⟨i, hi⟩
      exact (T.cover x).mpr ⟨i.1, hi.1⟩
  · intro i x hx t
    exact (T.roots_iff i.1 x hx.1 t).symm.trans ((hρ i.1 i.2).2.2 x hx.2 t)

end PlanarNikodym
