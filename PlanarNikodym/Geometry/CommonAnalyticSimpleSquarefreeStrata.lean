import PlanarNikodym.Geometry.CommonAnalyticPolynomialSquarefreeStrata
import PlanarNikodym.Geometry.AnalyticFractionResultant

/-! Common-domain squarefree branches with nonzero collision determinant on
the whole open ambient. The original carrier is preserved exactly. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure CommonAnalyticSimpleSquarefreeStratification
    {M : ℕ} (U V : Set E) (a : E → Fin M → ℝ)
    extends CommonAnalyticPolynomialSquarefreeStratification U V a where
  ambient_collision_ne_zero : ∀ i x, x ∈ (stratum i).ambient →
    weierstrassCollisionDet ((stratum i).coefficients x) ≠ 0

theorem exists_common_analytic_simple_squarefree_stratification
    {M : ℕ} (a : E → Fin M → ℝ) (U V : Set E) (hU : IsOpen U)
    (hV : CommonAnalyticOpen U V)
    (ha : ∀ i, AnalyticFractionOn U V (fun x => a x i)) :
    Nonempty (CommonAnalyticSimpleSquarefreeStratification U V a) := by
  classical
  obtain ⟨T⟩ := exists_common_analytic_fraction_squarefree_stratification a U V hU hV ha
  let Ω (i : T.Index) := (T.stratum i).ambient ∩
    {x | weierstrassCollisionDet ((T.stratum i).coefficients x) ≠ 0}
  have hΩ (i : T.Index) : CommonAnalyticOpen U (Ω i) :=
    (T.ambient_common i).inter_fraction_ne_zero
      (analyticFractionOn_weierstrassCollisionDet _ (T.coefficient_fraction i))
  let S (i : T.Index) : AnalyticPolynomialGcdStratumData E :=
    { T.stratum i with ambient := Ω i }
  refine ⟨{
    Index := T.Index
    indexFintype := T.indexFintype
    stratum := S
    ambient_open := fun i => (hΩ i).isOpen hU
    carrier_subset_ambient := fun i x hx => ⟨T.carrier_subset_ambient i hx, T.collision_ne_zero i x hx⟩
    ambient_subset_domain := fun i x hx => T.ambient_subset_domain i hx.1
    coefficients_analytic := fun i x hx => T.coefficients_analytic i x hx.1
    tests_analytic := fun i x hx => T.tests_analytic i x hx.1
    carrier_eq_tests := ?_
    degree_le := T.degree_le
    disjoint := T.disjoint
    cover := T.cover
    quotient_eq := T.quotient_eq
    collision_ne_zero := T.collision_ne_zero
    roots_iff := T.roots_iff
    ambient_common := hΩ
    coefficient_fraction := fun i j => (T.coefficient_fraction i j).mono inter_subset_left
    zero_test_fraction := fun i j => (T.zero_test_fraction i j).mono inter_subset_left
    ambient_collision_ne_zero := fun _ _ hx => hx.2 }⟩
  intro i x
  constructor
  · intro hx
    exact ⟨⟨T.carrier_subset_ambient i hx, T.collision_ne_zero i x hx⟩,
      ((T.carrier_eq_tests i x).mp hx).2⟩
  · rintro ⟨hx, ht⟩
    exact (T.carrier_eq_tests i x).mpr ⟨hx.1, ht⟩

theorem CommonAnalyticSimpleSquarefreeStratification.exists_common_analytic_tests
    {U V : Set E} {M : ℕ} {a : E → Fin M → ℝ}
    (T : CommonAnalyticSimpleSquarefreeStratification U V a) (i : T.Index) :
    ∃ (n : ℕ) (f : E → Fin n → ℝ) (g : E → Fin (T.stratum i).testCount → ℝ),
      AnalyticOnNhd ℝ f U ∧ AnalyticOnNhd ℝ g U ∧
      ∀ x, x ∈ (T.stratum i).carrier ↔
        x ∈ U ∧ (∀ j, f x j ≠ 0) ∧ ∀ j, g x j = 0 := by
  obtain ⟨n, f, hf, he⟩ := T.ambient_common i
  obtain ⟨g, hg, hge⟩ := exists_common_analytic_fraction_zero_tests
    (T.stratum i).zeroTests (T.zero_test_fraction i)
  refine ⟨n, f, g, hf, hg, ?_⟩
  intro x
  rw [T.carrier_eq_tests i x]
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨((he x).mp hx).1, ((he x).mp hx).2, (hge x hx).mp hz⟩
  · rintro ⟨hx, hn, hz⟩
    have hv := (he x).mpr ⟨hx, hn⟩
    exact ⟨hv, (hge x hv).mpr hz⟩

end PlanarNikodym
