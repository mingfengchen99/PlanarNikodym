import PlanarNikodym.Geometry.AnalyticStratificationSemianalyticPartition

/-! A simultaneous stratification of genuine semianalytic germs. Every
given set is an actual union of members of the constructed finite partition. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem exists_local_finite_semianalytic_stratification
    {d : ℕ} {J : Type} [Fintype J] (A : J → Set (Fin d → ℝ))
    (x₀ : Fin d → ℝ) (hA : ∀ j, SemianalyticAt (A j) x₀)
    (O : Set (Fin d → ℝ)) (hO : IsOpen O) (hxO : x₀ ∈ O) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x₀ ∈ U ∧ closure U ⊆ O ∧
      LocallySemianalytic U ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → AnalyticStratificationChart (Fin d → ℝ)),
        (⋃ i, (P i).image) = U ∧ Pairwise (fun i j => Disjoint (P i).image (P j).image) ∧
        (∀ i, LocallySemianalytic (P i).image) ∧ (∀ i, (P i).dim ≤ d) ∧
        (∀ i j, i ≠ j → ((P j).image ∩ closure (P i).image).Nonempty →
          (P j).image ⊆ closure (P i).image ∧ (P j).dim < (P i).dim) ∧
        ∀ j, A j ∩ U = ⋃ i : {i // (P i).image ⊆ A j}, (P i.val).image := by
  classical
  choose V hV hxV I hI f hf Q hrep using hA
  letI (j : J) : Fintype (I j) := hI j
  let F : (Σ j, I j) → (Fin d → ℝ) → ℝ := fun q => f q.1 q.2
  let W := O ∩ ⋂ j, V j
  have hW : IsOpen W := hO.inter (isOpen_iInter_of_finite hV)
  have hxW : x₀ ∈ W := ⟨hxO, mem_iInter.mpr hxV⟩
  obtain ⟨U, hU, hxU, hUW, hUsemi, ι, hι, P, hcover, hdisj, hsemi, hdim, hfront, hsign⟩ :=
    exists_local_finite_semianalytic_chart_stratification F x₀
      (fun q => hf q.1 q.2 x₀ (hxV q.1)) W hW hxW
  have hPiU (i : ι) : (P i).image ⊆ U := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hUVi {x : Fin d → ℝ} (hx : x ∈ U) (j : J) : x ∈ V j :=
    mem_iInter.mp (hUW (subset_closure hx)).2 j
  have hcompatible (i : ι) (j : J) (x y : Fin d → ℝ)
      (hx : x ∈ (P i).image) (hy : y ∈ (P i).image) : x ∈ A j ↔ y ∈ A j := by
    rw [hrep j x (hUVi (hPiU i hx) j), hrep j y (hUVi (hPiU i hy) j)]
    have he : (fun k => oneDimensionalSign (f j k x)) =
        fun k => oneDimensionalSign (f j k y) := by
      funext k
      exact hsign i ⟨j, k⟩ x hx y hy
    rw [he]
  refine ⟨U, hU, hxU, (fun x hx => (hUW hx).1), hUsemi,
    ι, hι, P, hcover, hdisj, hsemi, hdim, hfront, ?_⟩
  intro j
  ext x
  constructor
  · rintro ⟨hxA, hxU'⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ hxU')
    have hi : (P i).image ⊆ A j := fun y hy =>
      (hcompatible i j x y hxi hy).mp hxA
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact ⟨i.property hxi, hPiU i.val hxi⟩

end PlanarNikodym
