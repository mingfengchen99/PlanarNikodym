import PlanarNikodym.Geometry.AnalyticIntervalPartition
import Mathlib.Topology.Homeomorph.Lemmas

/-! Continuous sign refinement by a finite analytic separating family.
Only zero-set compatibility is supplied; sign constancy on connected cells
is proved by the intermediate value theorem. -/
noncomputable section
open Set
namespace PlanarNikodym

def analyticStrongSignCell {X I : Type*} (U : Set X)
    (f : I → X → ℝ) (s : I → Fin 3) : Set X :=
  {x | x ∈ U ∧ ∀ i, oneDimensionalSign (f i x) = s i}

theorem oneDimensionalSign_eq_of_preconnected_zero_dichotomy
    {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsPreconnected C)
    (f : X → ℝ) (hf : ContinuousOn f C)
    (hz : (∀ x ∈ C, f x = 0) ∨ (∀ x ∈ C, f x ≠ 0))
    {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    oneDimensionalSign (f x) = oneDimensionalSign (f y) := by
  rcases hz with hz | hn
  · rw [hz x hx, hz y hy]
  · rcases hC.mapsTo_Ioi_or_Iio hf hn with hp | hm
    · rw [oneDimensionalSign_eq_two.mpr (hp hx), oneDimensionalSign_eq_two.mpr (hp hy)]
    · rw [oneDimensionalSign_eq_zero.mpr (hm hx), oneDimensionalSign_eq_zero.mpr (hm hy)]

theorem analyticStrongSignCell_zero_dichotomy
    {X I J : Type*} (U : Set X) (f : I → X → ℝ) (g : J → X → ℝ)
    (hz : ∀ i, (∀ x ∈ U, f i x = 0) ∨
      ∃ j, ∀ x ∈ U, f i x = 0 ↔ g j x = 0)
    (t : J → Fin 3) (i : I) :
    (∀ x ∈ analyticStrongSignCell U g t, f i x = 0) ∨
      (∀ x ∈ analyticStrongSignCell U g t, f i x ≠ 0) := by
  classical
  rcases hz i with hf | ⟨j, hj⟩
  · exact Or.inl (fun x hx => hf x hx.1)
  · by_cases ht : t j = 1
    · left
      intro x hx
      apply (hj x hx.1).mpr
      exact oneDimensionalSign_eq_one.mp ((hx.2 j).trans ht)
    · right
      intro x hx hfx
      apply ht
      exact (hx.2 j).symm.trans (oneDimensionalSign_eq_one.mpr ((hj x hx.1).mp hfx))

/-- Adding the original functions to a connected separating family selects
one entire old sign cell, rather than a union or a disconnected subset. -/
theorem analyticStrongSignCell_sum_eq_right_or_empty
    {X I J : Type*} [TopologicalSpace X]
    (U : Set X) (f : I → X → ℝ) (g : J → X → ℝ)
    (hf : ∀ i, ContinuousOn (f i) U)
    (hz : ∀ i, (∀ x ∈ U, f i x = 0) ∨
      ∃ j, ∀ x ∈ U, f i x = 0 ↔ g j x = 0)
    (hg : ∀ t, analyticStrongSignCell U g t = ∅ ∨
      IsConnected (analyticStrongSignCell U g t))
    (s : I ⊕ J → Fin 3) :
    analyticStrongSignCell U (Sum.elim f g) s = ∅ ∨
      analyticStrongSignCell U (Sum.elim f g) s =
        analyticStrongSignCell U g (fun j => s (Sum.inr j)) := by
  classical
  rcases (analyticStrongSignCell U (Sum.elim f g) s).eq_empty_or_nonempty with he | hne
  · exact Or.inl he
  · right
    obtain ⟨a, ha⟩ := hne
    let t : J → Fin 3 := fun j => s (Sum.inr j)
    have haG : a ∈ analyticStrongSignCell U g t := ⟨ha.1, fun j => ha.2 (Sum.inr j)⟩
    have hconn : IsConnected (analyticStrongSignCell U g t) := by
      rcases hg t with he | hc
      · rw [he] at haG
        exact False.elim haG
      · exact hc
    apply Set.Subset.antisymm
    · exact fun x hx => ⟨hx.1, fun j => hx.2 (Sum.inr j)⟩
    · intro x hx
      refine ⟨hx.1, fun q => ?_⟩
      rcases q with i | j
      · have hconst := oneDimensionalSign_eq_of_preconnected_zero_dichotomy
          hconn.isPreconnected (f i) ((hf i).mono (fun _ hw => hw.1))
          (analyticStrongSignCell_zero_dichotomy U f g hz t i) hx haG
        exact hconst.trans (ha.2 (Sum.inl i))
      · exact hx.2 j

theorem analyticStrongSignCell_sum_connected_or_empty
    {X I J : Type*} [TopologicalSpace X]
    (U : Set X) (f : I → X → ℝ) (g : J → X → ℝ)
    (hf : ∀ i, ContinuousOn (f i) U)
    (hz : ∀ i, (∀ x ∈ U, f i x = 0) ∨
      ∃ j, ∀ x ∈ U, f i x = 0 ↔ g j x = 0)
    (hg : ∀ t, analyticStrongSignCell U g t = ∅ ∨
      IsConnected (analyticStrongSignCell U g t))
    (s : I ⊕ J → Fin 3) :
    analyticStrongSignCell U (Sum.elim f g) s = ∅ ∨
      IsConnected (analyticStrongSignCell U (Sum.elim f g) s) := by
  rcases analyticStrongSignCell_sum_eq_right_or_empty U f g hf hz hg s with he | he
  · exact Or.inl he
  · rw [he]
    exact hg _

end PlanarNikodym
