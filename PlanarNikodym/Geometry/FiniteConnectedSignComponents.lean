import PlanarNikodym.Geometry.AnalyticConnectedSeparation
import PlanarNikodym.Cells.AnalyticCellCover

/-! Actual finite connected components for arbitrary Boolean combinations
of a finite analytic germ family, on a constructed local neighborhood.
The component bound follows from the proved connected sign refinement. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem components_finite_of_finite_preconnected_cover
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {A : Set X} (C : κ → Set X) (hC : ∀ j, IsPreconnected (C j))
    (hsub : ∀ j, C j ⊆ A) (hcover : A ⊆ ⋃ j, C j) :
    (componentDomains A).Finite := by
  classical
  let J := {j : κ // (C j).Nonempty}
  choose u hu using fun j : J => j.2
  apply (Set.finite_range (fun j : J => connectedComponentIn A (u j))).subset
  rintro V ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
  let a : J := ⟨j, x, hj⟩
  refine ⟨a, ?_⟩
  exact connectedComponentIn_eq ((hC j).subset_connectedComponentIn (hu a) (hsub j) hj)

theorem component_eq_iUnion_of_finite_preconnected_cover
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {A : Set X} (C : κ → Set X) (hC : ∀ j, IsPreconnected (C j))
    (hsub : ∀ j, C j ⊆ A) (hcover : A ⊆ ⋃ j, C j) (x : X) :
    connectedComponentIn A x =
      ⋃ j : {j : κ // (C j ∩ connectedComponentIn A x).Nonempty}, C j := by
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (connectedComponentIn_subset A x hy))
    exact mem_iUnion.mpr ⟨⟨j, y, hj, hy⟩, hj⟩
  · intro hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨z, hzC, hzA⟩ := j.2
    rw [connectedComponentIn_eq hzA]
    exact (hC j).subset_connectedComponentIn hzC (hsub j) hj

theorem exists_local_finite_analytic_sign_component_cover
    {d : ℕ} {J : Type} [Fintype J] (f : J → (Fin d → ℝ) → ℝ)
    (x₀ : Fin d → ℝ) (hf : ∀ j, AnalyticAt ℝ (f j) x₀)
    (O : Set (Fin d → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O)
    (Q : (J → Fin 3) → Prop) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → (Fin d → ℝ) → ℝ)
        (S : Set (κ → Fin 3)),
        (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
        (∀ s ∈ S, IsConnected (analyticStrongSignCell U g s)) ∧
        {x | x ∈ U ∧ Q (fun j => oneDimensionalSign (f j x))} =
          ⋃ s : S, analyticStrongSignCell U g s := by
  classical
  obtain ⟨U, hU, hxU, hUO, κ, hκ, g, hg, hinc, hconn⟩ :=
    localAnalyticConnectedRefinement_fin d f x₀ hf O hO hxO
  choose k hk using hinc
  let S := {s : κ → Fin 3 | (analyticStrongSignCell U g s).Nonempty ∧
    Q (fun j => s (k j))}
  refine ⟨U, hU, hxU, hUO, κ, hκ, g, S, hg, ?_, ?_⟩
  · intro s hs
    rcases hconn s with he | hc
    · exact False.elim (hs.1.ne_empty he)
    · exact hc
  · ext x
    constructor
    · rintro ⟨hx, hQ⟩
      let s : κ → Fin 3 := fun j => oneDimensionalSign (g j x)
      have hcell : x ∈ analyticStrongSignCell U g s := ⟨hx, fun _ => rfl⟩
      have he : (fun j => oneDimensionalSign (f j x)) = fun j => s (k j) := by
        funext j
        exact congrArg oneDimensionalSign (hk j hx).symm
      exact mem_iUnion.mpr ⟨⟨s, ⟨⟨x, hcell⟩, he ▸ hQ⟩⟩, hcell⟩
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      refine ⟨hs.1, ?_⟩
      have he : (fun j => oneDimensionalSign (f j x)) = fun j => s.1 (k j) := by
        funext j
        rw [← hk j hs.1]
        exact hs.2 (k j)
      exact he.symm ▸ s.2.2

/-- Local finiteness of actual connected components, with no component or
cell input and no restriction on the Boolean predicate of the original signs. -/
theorem exists_local_finite_analytic_sign_components
    {d : ℕ} {J : Type} [Fintype J] (f : J → (Fin d → ℝ) → ℝ)
    (x₀ : Fin d → ℝ) (hf : ∀ j, AnalyticAt ℝ (f j) x₀)
    (O : Set (Fin d → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O)
    (Q : (J → Fin 3) → Prop) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
      (componentDomains {x | x ∈ U ∧ Q (fun j => oneDimensionalSign (f j x))}).Finite := by
  classical
  obtain ⟨U, hU, hxU, hUO, κ, hκ, g, S, hg, hconn, he⟩ :=
    exists_local_finite_analytic_sign_component_cover f x₀ hf O hO hxO Q
  refine ⟨U, hU, hxU, hUO, ?_⟩
  apply components_finite_of_finite_preconnected_cover
    (fun s : S => analyticStrongSignCell U g s)
    (fun s => (hconn s s.2).isPreconnected)
  · intro s x hx
    rw [he]
    exact mem_iUnion.mpr ⟨s, hx⟩
  · rw [he]

end PlanarNikodym
