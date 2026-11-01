import PlanarNikodym.Geometry.AnalyticStratificationSemianalyticCompatibility

/-! The actual relative frontier is a finite union of lower-dimensional
constructed strata. No frontier set or dimension estimate is supplied. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem stratum_relative_frontier_eq_union
    {E ι : Type} [TopologicalSpace E] {U : Set E} (S : ι → Set E)
    (hcover : (⋃ i, S i) = U) (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hfront : ∀ i j, i ≠ j → (S j ∩ closure (S i)).Nonempty → S j ⊆ closure (S i))
    (i : ι) :
    (closure (S i) ∩ U) \ S i =
      ⋃ j : {j // j ≠ i ∧ S j ⊆ closure (S i)}, S j.val := by
  ext x
  constructor
  · rintro ⟨⟨hxcl, hxU⟩, hxi⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover ▸ hxU)
    have hji : j ≠ i := fun he => hxi (he ▸ hxj)
    have hjcl := hfront i j (Ne.symm hji) ⟨x, hxj, hxcl⟩
    exact mem_iUnion.mpr ⟨⟨j, hji, hjcl⟩, hxj⟩
  · intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    refine ⟨⟨j.property.2 hxj, ?_⟩, ?_⟩
    · rw [← hcover]
      exact mem_iUnion.mpr ⟨j.val, hxj⟩
    · exact fun hxi => (Set.disjoint_left.mp (hdisj j.property.1)) hxj hxi

theorem stratum_relative_closure_eq_union
    {E ι : Type} [TopologicalSpace E] {U : Set E} (S : ι → Set E)
    (hcover : (⋃ i, S i) = U)
    (hfront : ∀ i j, i ≠ j → (S j ∩ closure (S i)).Nonempty → S j ⊆ closure (S i))
    (i : ι) :
    closure (S i) ∩ U = ⋃ j : {j // S j ⊆ closure (S i)}, S j.val := by
  ext x
  constructor
  · rintro ⟨hxcl, hxU⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover ▸ hxU)
    have hjcl : S j ⊆ closure (S i) := by
      by_cases hji : j = i
      · exact hji ▸ subset_closure
      · exact hfront i j (Ne.symm hji) ⟨x, hxj, hxcl⟩
    exact mem_iUnion.mpr ⟨⟨j, hjcl⟩, hxj⟩
  · intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    refine ⟨j.property hxj, ?_⟩
    rw [← hcover]
    exact mem_iUnion.mpr ⟨j.val, hxj⟩

theorem semianalytic_stratum_relative_frontier
    {d : ℕ} {ι : Type} [Fintype ι] {U : Set (Fin d → ℝ)}
    (P : ι → AnalyticStratificationChart (Fin d → ℝ))
    (hcover : (⋃ i, (P i).image) = U)
    (hdisj : Pairwise (fun i j => Disjoint (P i).image (P j).image))
    (hsemi : ∀ i, LocallySemianalytic (P i).image)
    (hfront : ∀ i j, i ≠ j → ((P j).image ∩ closure (P i).image).Nonempty →
      (P j).image ⊆ closure (P i).image ∧ (P j).dim < (P i).dim)
    (i : ι) :
    LocallySemianalytic ((closure (P i).image ∩ U) \ (P i).image) ∧
      (∀ j, j ≠ i → ((P j).image ∩ closure (P i).image).Nonempty →
        (P j).dim < (P i).dim) := by
  classical
  refine ⟨?_, fun j hji hne => (hfront i j (Ne.symm hji) hne).2⟩
  rw [stratum_relative_frontier_eq_union (fun j => (P j).image) hcover hdisj
    (fun a b hab hne => (hfront a b hab hne).1)]
  exact LocallySemianalytic.iUnion _ (fun j => hsemi j.val)

theorem semianalytic_stratum_relative_closure
    {d : ℕ} {ι : Type} [Fintype ι] {U : Set (Fin d → ℝ)}
    (P : ι → AnalyticStratificationChart (Fin d → ℝ))
    (hcover : (⋃ i, (P i).image) = U)
    (hsemi : ∀ i, LocallySemianalytic (P i).image)
    (hfront : ∀ i j, i ≠ j → ((P j).image ∩ closure (P i).image).Nonempty →
      (P j).image ⊆ closure (P i).image) (i : ι) :
    LocallySemianalytic (closure (P i).image ∩ U) := by
  classical
  rw [stratum_relative_closure_eq_union (fun j => (P j).image) hcover hfront]
  exact LocallySemianalytic.iUnion _ (fun j => hsemi j.val)

end PlanarNikodym
