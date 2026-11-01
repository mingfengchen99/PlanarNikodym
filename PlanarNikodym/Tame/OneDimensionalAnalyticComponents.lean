import PlanarNikodym.Geometry.AnalyticIntervalPartition
import PlanarNikodym.Tame.RestrictedAnalyticSets
import PlanarNikodym.Cells.AnalyticCellCover

/-! One-dimensional compact analytic sign sets have finitely many actual
connected components, and every component is definable in the existing
restricted analytic language. No o-minimality or component axiom is used:
components are finite unions of the constructed interval atoms. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem ranDefinable_oneDimensionalSign_fiber (a : ℝ) (c : Fin 3) :
    RanDefinable {x : Fin 1 → ℝ | oneDimensionalSign (x 0 - a) = c} := by
  fin_cases c
  · change RanDefinable {x : Fin 1 → ℝ | oneDimensionalSign (x 0 - a) = 0}
    simpa only [oneDimensionalSign_eq_zero, sub_neg] using
      ranDefinable_lt (ranDefinableFun_coordinate (0 : Fin 1)) (ranDefinableFun_const a)
  · change RanDefinable {x : Fin 1 → ℝ | oneDimensionalSign (x 0 - a) = 1}
    have h := (ranDefinable_le (ranDefinableFun_coordinate (0 : Fin 1))
      (ranDefinableFun_const a)).inter
        (ranDefinable_le (ranDefinableFun_const a) (ranDefinableFun_coordinate (0 : Fin 1)))
    convert h using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, oneDimensionalSign_eq_one, sub_eq_zero]
    exact le_antisymm_iff
  · change RanDefinable {x : Fin 1 → ℝ | oneDimensionalSign (x 0 - a) = 2}
    simpa only [oneDimensionalSign_eq_two, sub_pos] using
      ranDefinable_lt (ranDefinableFun_const a) (ranDefinableFun_coordinate (0 : Fin 1))

theorem ranDefinable_analyticIntervalAtom (I : Interval) (S : Finset ℝ) (σ : S → Fin 3) :
    RanDefinable {x : Fin 1 → ℝ | x 0 ∈ analyticIntervalAtom I S σ} := by
  have hI : RanDefinable {x : Fin 1 → ℝ | x 0 ∈ I.carrier} :=
    (ranDefinable_le (ranDefinableFun_const I.left) (ranDefinableFun_coordinate (0 : Fin 1))).inter
      (ranDefinable_le (ranDefinableFun_coordinate (0 : Fin 1)) (ranDefinableFun_const I.right))
  have hS := Set.definable_iInter_of_finite
    (fun z : S => ranDefinable_oneDimensionalSign_fiber z (σ z))
  convert hI.inter hS using 1
  ext x
  simp only [analyticIntervalAtom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

/-- A finite preconnected cover inside a set bounds its actual nonempty
connected components. This is a topological lemma, not a finiteness field. -/
theorem oneDimensional_components_finite_of_finite_cover {κ : Type*} [Fintype κ]
    {E : Set ℝ} (C : κ → Set ℝ) (hC : ∀ j, IsPreconnected (C j))
    (hsub : ∀ j, C j ⊆ E) (hcover : E ⊆ ⋃ j, C j) :
    (componentDomains E).Finite := by
  classical
  let J := {j : κ // (C j).Nonempty}
  choose u hu using fun j : J => j.2
  apply (Set.finite_range (fun j : J => connectedComponentIn E (u j))).subset
  rintro V ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
  let a : J := ⟨j, x, hj⟩
  refine ⟨a, ?_⟩
  exact connectedComponentIn_eq
    ((hC j).subset_connectedComponentIn (hu a) (hsub j) hj)

/-- Each component of a finite preconnected cover is precisely the union
of those cover pieces that meet it. -/
theorem oneDimensional_component_eq_union {κ : Type*} [Fintype κ]
    {E : Set ℝ} (C : κ → Set ℝ) (hC : ∀ j, IsPreconnected (C j))
    (hsub : ∀ j, C j ⊆ E) (hcover : E ⊆ ⋃ j, C j) (x : ℝ) :
    connectedComponentIn E x =
      ⋃ j : {j : κ // (C j ∩ connectedComponentIn E x).Nonempty}, C j := by
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (connectedComponentIn_subset E x hy))
    exact mem_iUnion.mpr ⟨⟨j, y, hj, hy⟩, hj⟩
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨z, hzC, hzE⟩ := j.2
    rw [connectedComponentIn_eq hzE]
    exact (hC j).subset_connectedComponentIn hzC (hsub j) hj

theorem ranDefinable_oneDimensional_component_of_finite_cover
    {κ : Type*} [Fintype κ] {E : Set ℝ} (C : κ → Set ℝ)
    (hC : ∀ j, IsPreconnected (C j)) (hsub : ∀ j, C j ⊆ E)
    (hcover : E ⊆ ⋃ j, C j)
    (hdef : ∀ j, RanDefinable {y : Fin 1 → ℝ | y 0 ∈ C j}) (x : ℝ) :
    RanDefinable {y : Fin 1 → ℝ | y 0 ∈ connectedComponentIn E x} := by
  rw [oneDimensional_component_eq_union C hC hsub hcover x]
  convert Set.definable_iUnion_of_finite
    (fun j : {j : κ // (C j ∩ connectedComponentIn E x).Nonempty} => hdef j) using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]

/-- Any Boolean combination of the signs of a fixed finite analytic
family on the compact interval has a genuine finite connected cover by
explicit definable interval atoms. `Q` is completely arbitrary. -/
theorem exists_oneDimensional_analytic_sign_cover {ι : Type*} [Fintype ι]
    (I : Interval) (f : ι → ℝ → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier)
    (Q : (ι → Fin 3) → Prop) :
    ∃ (S : Finset ℝ) (C : (S → Fin 3) → Set ℝ),
      (∀ σ, IsPreconnected (C σ)) ∧
      (∀ σ, RanDefinable {x : Fin 1 → ℝ | x 0 ∈ C σ}) ∧
      (∀ σ, C σ ⊆ {x | x ∈ I.carrier ∧ Q (fun i => oneDimensionalSign (f i x))}) ∧
      {x | x ∈ I.carrier ∧ Q (fun i => oneDimensionalSign (f i x))} ⊆ ⋃ σ, C σ := by
  classical
  obtain ⟨S, _, _, _, hconn, hsign⟩ := exists_analytic_interval_sign_partition I f hf
  choose v hv using hsign
  let C (σ : S → Fin 3) : Set ℝ :=
    if Q (v σ) then analyticIntervalAtom I S σ else ∅
  refine ⟨S, C, ?_, ?_, ?_, ?_⟩
  · intro σ
    dsimp [C]
    split_ifs
    · exact (hconn σ).isPreconnected
    · exact isPreconnected_empty
  · intro σ
    dsimp [C]
    split_ifs
    · exact ranDefinable_analyticIntervalAtom I S σ
    · simp
  · intro σ x hx
    dsimp [C] at hx
    split_ifs at hx with hQ
    · have he : (fun i => oneDimensionalSign (f i x)) = v σ :=
        funext (hv σ x hx)
      exact ⟨hx.1, he.symm ▸ hQ⟩
    · exact (Set.notMem_empty x hx).elim
  · intro x hx
    let σ : S → Fin 3 := fun z => oneDimensionalSign (x - z)
    have ha : x ∈ analyticIntervalAtom I S σ := ⟨hx.1, fun _ => rfl⟩
    have he : (fun i => oneDimensionalSign (f i x)) = v σ := funext (hv σ x ha)
    have hQ : Q (v σ) := he ▸ hx.2
    exact mem_iUnion.mpr ⟨σ, by simpa [C, hQ] using ha⟩

/-- Finite actual connected components and definability of every such
component, for one-dimensional compact analytic sign sets. This does not
assert the corresponding statement for higher dimensions or projections. -/
theorem oneDimensional_analytic_sign_components {ι : Type*} [Fintype ι]
    (I : Interval) (f : ι → ℝ → ℝ) (hf : ∀ i, AnalyticOnNhd ℝ (f i) I.carrier)
    (Q : (ι → Fin 3) → Prop) :
    let E := {x | x ∈ I.carrier ∧ Q (fun i => oneDimensionalSign (f i x))}
    (componentDomains E).Finite ∧
      ∀ x : ℝ, RanDefinable {y : Fin 1 → ℝ | y 0 ∈ connectedComponentIn E x} := by
  classical
  obtain ⟨S, C, hC, hdef, hsub, hcover⟩ := exists_oneDimensional_analytic_sign_cover I f hf Q
  exact ⟨oneDimensional_components_finite_of_finite_cover C hC hsub hcover,
    ranDefinable_oneDimensional_component_of_finite_cover C hC hsub hcover hdef⟩

end PlanarNikodym
