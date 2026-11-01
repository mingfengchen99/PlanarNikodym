import PlanarNikodym.Cells.SemianalyticClosureHausdorff

/-! The missing boundary `closure A \ A` of a semianalytic set has
strictly smaller integer dimension. This is distinct from its topological
frontier, which can contain all of a lower-dimensional set. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal Topology
namespace PlanarNikodym

theorem SemianalyticAt.exists_open_missing_boundary_strata
    {n : ℕ} {A : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hA : SemianalyticAt A x) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → AnalyticStratificationChart (Fin n → ℝ)),
        (closure A \ A) ∩ U = ⋃ i, (P i).image ∧
        ∀ i, ((P i).dim + 1 : ℝ≥0∞) ≤ dimH A := by
  classical
  obtain ⟨U, hU, hxU, _, _, ι, hι, P, hcover, hdisj, _, _, hfront, hrep⟩ :=
    exists_local_finite_semianalytic_stratification (fun _ : Unit => A) x
      (fun _ => hA) univ isOpen_univ (mem_univ _)
  let I := {i : ι // (P i).image ⊆ A}
  have hPiU (i : ι) : (P i).image ⊆ U := by
    intro y hy
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hecl : closure (A ∩ U) = ⋃ i : I, closure (P i.val).image := by
    rw [hrep (), closure_iUnion_of_finite]
  have hdisjA (j : ι) (hj : ¬ (P j).image ⊆ A) : Disjoint (P j).image A := by
    apply Set.disjoint_left.mpr
    intro y hyj hyA
    have hy : y ∈ A ∩ U := ⟨hyA, hPiU j hyj⟩
    rw [hrep ()] at hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    by_cases hji : j = i.val
    · exact hj (hji ▸ i.property)
    · exact (Set.disjoint_left.mp (hdisj hji)) hyj hyi
  have hsource {y : Fin n → ℝ} (hy : y ∈ closure A ∩ U) :
      ∃ i : I, y ∈ closure (P i.val).image := by
    have hy' := hU.closure_inter hy
    rw [hecl] at hy'
    exact mem_iUnion.mp hy'
  let T := {j : ι // (P j).image ⊆ closure A ∧ Disjoint (P j).image A}
  have hTdim (j : T) : ((P j.val).dim + 1 : ℝ≥0∞) ≤ dimH A := by
    obtain ⟨y, hyj⟩ := (P j.val).connected_image.nonempty
    obtain ⟨i, hyi⟩ := hsource ⟨j.property.1 hyj, hPiU j.val hyj⟩
    have hij : i.val ≠ j.val := by
      intro he
      have hyA : y ∈ A := i.property (by rwa [he])
      exact Set.disjoint_left.mp j.property.2 hyj hyA
    have hd := (hfront i.val j.val hij ⟨y, hyj, hyi⟩).2
    have hiD : ((P i.val).dim : ℝ≥0∞) ≤ dimH A := by
      rw [← (P i.val).dimH_image]
      exact dimH_mono i.property
    have hjiD : ((P j.val).dim + 1 : ℝ≥0∞) ≤ (P i.val).dim := by
      exact_mod_cast Nat.succ_le_of_lt hd
    exact hjiD.trans hiD
  refine ⟨U, hU, hxU, T, inferInstance, (fun j => P j.val), ?_, hTdim⟩
  ext y
  constructor
  · rintro ⟨⟨hycl, hynA⟩, hyU⟩
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover ▸ hyU)
    obtain ⟨i, hyi⟩ := hsource ⟨hycl, hyU⟩
    have hjA : ¬ (P j).image ⊆ A := fun hj => hynA (hj hyj)
    have hij : i.val ≠ j := by
      intro he
      exact hjA (he ▸ i.property)
    have hjcl : (P j).image ⊆ closure A :=
      ((hfront i.val j hij ⟨y, hyj, hyi⟩).1).trans (closure_mono i.property)
    exact mem_iUnion.mpr ⟨⟨j, hjcl, hdisjA j hjA⟩, hyj⟩
  · intro hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    exact ⟨⟨j.property.1 hyj, fun hyA => Set.disjoint_left.mp j.property.2 hyj hyA⟩,
      hPiU j.val hyj⟩

theorem LocallySemianalytic.dimH_missing_boundary_le {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : LocallySemianalytic A) (k : ℕ) (hdim : dimH A ≤ (k + 1 : ℕ)) :
    dimH (closure A \ A) ≤ k := by
  classical
  by_contra hle
  obtain ⟨x, _, hlarge⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (lt_of_not_ge hle)
  obtain ⟨U, hU, hxU, ι, hι, P, heq, hPdim⟩ :=
    SemianalyticAt.exists_open_missing_boundary_strata (hA x)
  have hbound : dimH ((closure A \ A) ∩ U) ≤ k := by
    rw [heq, dimH_iUnion]
    apply iSup_le
    intro i
    rw [(P i).dimH_image]
    have hd : (P i).dim + 1 ≤ k + 1 := by exact_mod_cast (hPdim i).trans hdim
    exact_mod_cast (show (P i).dim ≤ k by omega)
  exact (not_lt_of_ge hbound)
    (hlarge ((closure A \ A) ∩ U) (inter_mem_nhdsWithin _ (hU.mem_nhds hxU)))

theorem LocallySemianalytic.missing_boundary_eq_empty_of_dimH_zero
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A) (hdim : dimH A = 0) :
    closure A \ A = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨U, _, hxU, ι, hι, P, heq, hPdim⟩ :=
    SemianalyticAt.exists_open_missing_boundary_strata (hA x)
  have hx' : x ∈ ⋃ i, (P i).image := heq ▸ ⟨hx, hxU⟩
  obtain ⟨i, _⟩ := mem_iUnion.mp hx'
  have hd : (P i).dim + 1 ≤ 0 := by exact_mod_cast (hPdim i).trans_eq hdim
  omega

theorem LocallySemianalytic.isClosed_of_dimH_zero
    {n : ℕ} {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A) (hdim : dimH A = 0) :
    IsClosed A := by
  apply isClosed_of_closure_subset
  intro x hx
  by_contra hn
  have hx' : x ∈ closure A \ A := ⟨hx, hn⟩
  rw [hA.missing_boundary_eq_empty_of_dimH_zero hdim] at hx'
  exact hx'

end PlanarNikodym
