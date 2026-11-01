import PlanarNikodym.Cells.PlanarOpenRankRegions
import PlanarNikodym.Cells.FullDimensionalRankStrata
import PlanarNikodym.Cells.FamilyCriticalCenterCover

/-! Actual finite disjoint rank decomposition in zero auxiliary dimension.
The parent can be any bounded semianalytic source whose closure is inside
an open analytic parameter neighborhood. No cell input is an assumption. -/
noncomputable section
open Set Module MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem Family.exists_zero_auxiliary_finite_rankDecomposition_on_source
    (G : Family 2 0) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (S : Set (Fin 2 → ℝ)) (hS : LocallySemianalytic S)
    (hb : Bornology.IsBounded S) (hSW : closure S ⊆ (parameterFrame 0) ⁻¹' G.W) :
    Nonempty (RankDecomposition (G.restrictTo ((parameterFrame 0) '' S))) := by
  classical
  let H := G.restrictTo ((parameterFrame 0) '' S)
  have hHS : (parameterFrame 0) '' S ⊆ G.W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hSW (subset_closure hx)
  have hHa : H.IsAnalytic := ha.restrictTo hHS
  obtain ⟨ι, hι, P, hcover, E, _, hEc, hEn, _, _, hcritical⟩ :=
    G.exists_intrinsic_rank_cover_with_critical_exception ho ha S hS hb hSW
  have hPS (i : ι) : (P i).chart.image ⊆ S := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hdim (i : ι) : (P i).chart.dim ≤ 2 := by
    have hd := (dimH_mono (subset_univ (P i).chart.image)).trans_eq (Real.dimH_univ_pi_fin 2)
    rw [(P i).chart.dimH_image] at hd
    exact_mod_cast hd
  have hfull (i : ι) (hi : ¬ (P i).centerCritical) : (P i).chart.dim = 2 := by
    by_contra hn
    have hd : (P i).chart.dim ≤ 1 := by have h := hdim i; omega
    obtain ⟨q, hq⟩ := (P i).chart.connected_source.nonempty
    apply hi
    refine ⟨q, hq, ?_⟩
    have hr := LinearMap.finrank_range_le
      ((parameterCenterDerivative 0).toLinearMap.comp
        (fderiv ℝ (P i).chart.map q).toLinearMap)
    rw [finrank_fin_fun] at hr
    exact hr.trans hd
  let J := {i : ι // ¬ (P i).centerCritical}
  let f : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let C (i : Fin (Fintype.card J)) := (P (f i).val).chart.image
  have hCW (i : Fin (Fintype.card J)) : (parameterFrame 0) '' C i ⊆ H.W :=
    image_mono (hPS (f i).val)
  have hex (i : Fin (Fintype.card J)) : ∃ mp mc : ℕ,
      ∀ x ∈ C i, H.pointRank (parameterFrame 0 x) = mp ∧
        H.curveRank (parameterFrame 0 x) = mc := by
    obtain ⟨mp, mc, hr⟩ := (P (f i).val).constant_ranks_on_full_dimensional_image
      (G := H) hHa (hCW i) (hb.subset (hPS (f i).val))
      (hfull (f i).val (f i).property)
    exact ⟨mp, mc, fun x hx => hr _ (mem_image_of_mem _ hx)⟩
  choose mp mc hr using hex
  apply H.exists_zero_auxiliary_rankDecomposition_of_finite_open_cover hHa C
    (fun i => (P (f i).val).chart.isOpen_image_of_dim_eq
      (hfull (f i).val (f i).property))
    (fun i => (P (f i).val).semianalytic)
    (fun i => hb.subset (hPS (f i).val)) hCW mp mc hr E hEc.isClosed hEn
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ hx)
  by_cases hi : (P i).centerCritical
  · exact Or.inl (hcritical i hi (subset_closure
      (mem_image_of_mem (parameterCenterDerivative 0) hxi)))
  · apply Or.inr
    refine ⟨f.symm ⟨i, hi⟩, ?_⟩
    change (parameterFrame 0).symm (parameterFrame 0 x) ∈ (P (f (f.symm ⟨i, hi⟩)).val).chart.image
    rw [(parameterFrame 0).symm_apply_apply, f.apply_symm_apply]
    exact hxi

end PlanarNikodym
