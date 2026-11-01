import PlanarNikodym.Cells.AnalyticStratumIntrinsicDimension
import PlanarNikodym.Geometry.AnalyticStratificationFrontierUnions

/-! The actual Hausdorff dimension of a stratum is preserved by taking
its closure inside the constructed finite stratification window. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem stratum_relative_closure_dimH
    {n : ℕ} {ι : Type} [Fintype ι]
    (P : ι → AnalyticStratificationChart (Fin n → ℝ))
    {U : Set (Fin n → ℝ)} (hcover : (⋃ i, (P i).image) = U)
    (hfront : ∀ i j, i ≠ j → ((P j).image ∩ closure (P i).image).Nonempty →
      (P j).image ⊆ closure (P i).image ∧ (P j).dim < (P i).dim)
    (i : ι) : dimH (closure (P i).image ∩ U) = (P i).dim := by
  apply le_antisymm
  · rw [stratum_relative_closure_eq_union (fun j => (P j).image) hcover
      (fun a b hab hne => (hfront a b hab hne).1), dimH_iUnion]
    apply iSup_le
    intro j
    rw [(P j.val).dimH_image]
    have hd : (P j.val).dim ≤ (P i).dim := by
      by_cases hji : j.val = i
      · simp only [hji, le_refl]
      · obtain ⟨x, hx⟩ := (P j.val).connected_image.nonempty
        exact ((hfront i j.val (Ne.symm hji) ⟨x, hx, j.property hx⟩).2).le
    exact_mod_cast hd
  · rw [← (P i).dimH_image]
    apply dimH_mono
    intro x hx
    refine ⟨subset_closure hx, ?_⟩
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩

end PlanarNikodym
