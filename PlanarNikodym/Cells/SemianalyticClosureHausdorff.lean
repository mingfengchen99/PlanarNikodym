import PlanarNikodym.Cells.StratumRelativeClosureDimension

/-! Hausdorff dimension is preserved by closure for genuine semianalytic
sets. The actual compatible finite strata prove the local statement;
second countability removes any boundedness assumption globally. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal Topology
namespace PlanarNikodym

theorem SemianalyticAt.exists_open_dimH_closure_inter_eq
    {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hA : SemianalyticAt A x) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧
      dimH (closure A ∩ U) = dimH (A ∩ U) := by
  classical
  obtain ⟨U, hU, hxU, _, _, ι, hι, P, hcover, _, _, _, hfront, hrep⟩ :=
    exists_local_finite_semianalytic_stratification (fun _ : Unit => A) x
      (fun _ => hA) univ isOpen_univ (mem_univ _)
  let T := {i : ι // (P i).image ⊆ A}
  have hPiU (i : ι) : (P i).image ⊆ U := by
    intro y hy
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hecl : closure (A ∩ U) = ⋃ i : T, closure (P i.val).image := by
    rw [hrep (), closure_iUnion_of_finite]
  have hsub : closure A ∩ U ⊆ ⋃ i : T, closure (P i.val).image ∩ U := by
    rintro y ⟨hy, hyU⟩
    have hy' := hU.closure_inter ⟨hy, hyU⟩
    rw [hecl] at hy'
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy'
    exact mem_iUnion.mpr ⟨i, hyi, hyU⟩
  refine ⟨U, hU, hxU, le_antisymm ?_ ?_⟩
  · calc
      dimH (closure A ∩ U) ≤ dimH (⋃ i : T, closure (P i.val).image ∩ U) := dimH_mono hsub
      _ = ⨆ i : T, dimH (closure (P i.val).image ∩ U) := dimH_iUnion _
      _ ≤ dimH (A ∩ U) := by
        apply iSup_le
        intro i
        rw [stratum_relative_closure_dimH P hcover hfront i.val, ← (P i.val).dimH_image]
        exact dimH_mono (fun y hy => ⟨i.property hy, hPiU i.val hy⟩)
  · exact dimH_mono (inter_subset_inter_left U subset_closure)

theorem LocallySemianalytic.dimH_closure {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : LocallySemianalytic A) : dimH (closure A) = dimH A := by
  apply le_antisymm ?_ (dimH_mono subset_closure)
  by_contra hle
  have hlt : dimH A < dimH (closure A) := lt_of_not_ge hle
  obtain ⟨x, _, hlarge⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hlt
  obtain ⟨U, hU, hxU, heq⟩ :=
    SemianalyticAt.exists_open_dimH_closure_inter_eq (hA x)
  have hbound : dimH (closure A ∩ U) ≤ dimH A :=
    heq.le.trans (dimH_mono inter_subset_left)
  exact (not_lt_of_ge hbound)
    (hlarge (closure A ∩ U) (inter_mem_nhdsWithin (closure A) (hU.mem_nhds hxU)))

end PlanarNikodym
