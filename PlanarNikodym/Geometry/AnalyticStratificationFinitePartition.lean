import PlanarNikodym.Geometry.AnalyticStratificationInduction
import PlanarNikodym.Geometry.AnalyticStratificationFrontier

/-! A finite disjoint actual analytic chart partition from the original
finite analytic germs. This makes the constructed maps and dimensions
available without any supplied stratification or chart decomposition. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem exists_local_finite_analytic_stratum_partition
    {d : ℕ} {J : Type} [Fintype J] (f : J → (Fin d → ℝ) → ℝ)
    (x₀ : Fin d → ℝ) (ha : ∀ j, AnalyticAt ℝ (f j) x₀)
    (O : Set (Fin d → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → AnalyticStratificationChart (Fin d → ℝ)),
        (⋃ i, (P i).image) = U ∧ Pairwise (fun i j => Disjoint (P i).image (P j).image) ∧
        (∀ i, (P i).dim ≤ d) ∧
        (∀ i j, ((P j).image ∩ closure (P i).image).Nonempty →
          (P j).image ⊆ closure (P i).image) ∧
        ∀ i j, ∀ x ∈ (P i).image, ∀ y ∈ (P i).image,
          oneDimensionalSign (f j x) = oneDimensionalSign (f j y) := by
  classical
  obtain ⟨U, hU, hxU, hUO, κ, hκ, g, hg, hinc, href⟩ :=
    localAnalyticStratumRefinement_fin d f x₀ ha O hO hxO
  let S := {s : κ → Fin 3 // (analyticStrongSignCell U g s).Nonempty}
  have hchart (s : S) : ∃ P : AnalyticStratificationChart (Fin d → ℝ),
      P.image = analyticStrongSignCell U g s ∧
        closure (analyticStrongSignCell U g s) ∩ U = analyticWeakSignCell U g s := by
    rcases href s with he | h
    · exact False.elim (s.property.ne_empty he)
    · exact h
  choose P hP hcl using hchart
  refine ⟨U, hU, hxU, hUO, S, inferInstance, P, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      rw [hP s] at hs
      exact hs.1
    · intro hx
      let s : κ → Fin 3 := fun k => oneDimensionalSign (g k x)
      have hs : x ∈ analyticStrongSignCell U g s := ⟨hx, fun _ => rfl⟩
      let a : S := ⟨s, x, hs⟩
      exact mem_iUnion.mpr ⟨a, (Set.ext_iff.mp (hP a) x).mpr hs⟩
  · intro s t hst
    apply Set.disjoint_left.mpr
    intro x hxs hxt
    rw [hP s] at hxs
    rw [hP t] at hxt
    apply hst
    apply Subtype.ext
    exact funext (fun k => (hxs.2 k).symm.trans (hxt.2 k))
  · intro i
    simpa using (P i).dim_le_finrank
  · intro i j hne
    rw [hP i, hP j] at hne ⊢
    exact analyticStrongSignCell_subset_closure_of_inter U g i j (hcl i) hne
  · intro i j x hx y hy
    obtain ⟨k, hk⟩ := hinc j
    rw [hP i] at hx hy
    rw [← hk hx.1, ← hk hy.1]
    exact (hx.2 k).trans (hy.2 k).symm

end PlanarNikodym
