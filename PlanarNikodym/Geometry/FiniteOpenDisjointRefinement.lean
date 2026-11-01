import PlanarNikodym.Geometry.AnalyticStratificationSemianalyticClosure

/-! Finite open pieces can be made disjoint by removing earlier closures.
The precise lost set is contained in the finite union of their frontiers;
no assertion about the dimension of its projection is hidden here. -/
noncomputable section
open Set
namespace PlanarNikodym

def finiteOpenDisjointPatch {X : Type*} [TopologicalSpace X] {N : ℕ}
    (C : Fin N → Set X) (i : Fin N) : Set X :=
  C i \ ⋃ j : {j : Fin N // j < i}, closure (C j.val)

theorem finiteOpenDisjointPatch_subset {X : Type*} [TopologicalSpace X] {N : ℕ}
    (C : Fin N → Set X) (i : Fin N) : finiteOpenDisjointPatch C i ⊆ C i :=
  sdiff_subset

theorem finiteOpenDisjointPatch_isOpen {X : Type*} [TopologicalSpace X] {N : ℕ}
    (C : Fin N → Set X) (hC : ∀ i, IsOpen (C i)) (i : Fin N) :
    IsOpen (finiteOpenDisjointPatch C i) :=
  (hC i).sdiff (isClosed_iUnion_of_finite (fun _ => isClosed_closure))

theorem finiteOpenDisjointPatch_pairwise {X : Type*} [TopologicalSpace X] {N : ℕ}
    (C : Fin N → Set X) : Pairwise (fun i j =>
      Disjoint (finiteOpenDisjointPatch C i) (finiteOpenDisjointPatch C j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hxj.2 (mem_iUnion.mpr ⟨⟨i, h⟩, subset_closure hxi.1⟩)
  · exact hxi.2 (mem_iUnion.mpr ⟨⟨j, h⟩, subset_closure hxj.1⟩)

theorem finiteOpenDisjointPatch_cover {X : Type*} [TopologicalSpace X] {N : ℕ}
    (C : Fin N → Set X) {x : X} (hx : x ∈ ⋃ i, C i) :
    x ∈ ⋃ i, frontier (C i) ∨ ∃ i, x ∈ finiteOpenDisjointPatch C i := by
  classical
  by_cases hf : x ∈ ⋃ i, frontier (C i)
  · exact Or.inl hf
  apply Or.inr
  let s := Finset.univ.filter (fun i => x ∈ C i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := s.min' hs
  have hi : x ∈ C i := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  refine ⟨i, hi, ?_⟩
  intro hbad
  obtain ⟨j, hj⟩ := mem_iUnion.mp hbad
  have hn : x ∉ frontier (C j.val) := fun h => hf (mem_iUnion.mpr ⟨j.val, h⟩)
  have hc : x ∈ C j.val := interior_subset (by
    by_contra h
    exact hn ⟨hj, h⟩)
  have hjs : j.val ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  exact (not_lt_of_ge (Finset.min'_le s j.val hjs)) j.property

theorem LocallySemianalytic.finiteOpenDisjointPatch {n N : ℕ}
    {C : Fin N → Set (Fin n → ℝ)} (hC : ∀ i, LocallySemianalytic (C i)) (i : Fin N) :
    LocallySemianalytic (finiteOpenDisjointPatch C i) :=
  (hC i).inter ((LocallySemianalytic.iUnion
    (fun j : {j : Fin N // j < i} => _root_.closure (C j.val))
    (fun j => (hC j.val).closure)).compl)

end PlanarNikodym
