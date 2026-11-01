import PlanarNikodym.Cells.AnalyticStratumHausdorff
import PlanarNikodym.Geometry.AnalyticStratificationSemianalyticClosure
import PlanarNikodym.Tame.DefinableContinuousImageComponents

/-! Genuine compact windows for low-dimensional analytic strata. Strict
frontier dimensions control the closure inside the actual finite
stratification, without assuming a compact extension of any chart map. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

def stratumCompactProjectionException {n : ℕ} {ι : Type} [Fintype ι]
    (P : ι → AnalyticStratificationChart (Fin n → ℝ)) (K : Set (Fin n → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] Base 2) : Set (Base 2) :=
  ⋃ i : {i : ι // (P i).dim < 2}, L '' (closure (P i.val).image ∩ K)

theorem finite_strata_compact_low_dimensional_exception
    {n : ℕ} {ι : Type} [Fintype ι]
    (P : ι → AnalyticStratificationChart (Fin n → ℝ))
    {U : Set (Fin n → ℝ)} (hcover : (⋃ i, (P i).image) = U)
    (hfront : ∀ i j, i ≠ j → ((P j).image ∩ closure (P i).image).Nonempty →
      (P j).image ⊆ closure (P i).image ∧ (P j).dim < (P i).dim)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKU : K ⊆ U)
    (L : (Fin n → ℝ) →L[ℝ] Base 2) :
    IsClosed (stratumCompactProjectionException P K L) ∧
      volume (stratumCompactProjectionException P K L) = 0 ∧
      ∀ i, (P i).dim < 2 → closure (L '' ((P i).image ∩ K)) ⊆
        stratumCompactProjectionException P K L := by
  classical
  let J := {i : ι // (P i).dim < 2}
  let C (i : J) := L '' (closure (P i.val).image ∩ K)
  have hcompact (i : J) : IsCompact (C i) :=
    (hK.inter_left isClosed_closure).image L.continuous
  have hnull (i : J) : volume (C i) = 0 := by
    have hsub : C i ⊆ ⋃ j : J, L '' (P j.val).image := by
      rintro y ⟨x, hx, rfl⟩
      have hxU : x ∈ ⋃ j, (P j).image := hcover ▸ hKU hx.2
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxU
      have hjdim : (P j).dim < 2 := by
        by_cases hji : j = i.val
        · simpa only [hji] using i.property
        · exact ((hfront i.val j (Ne.symm hji) ⟨x, hxj, hx.1⟩).2).trans i.property
      exact mem_iUnion.mpr ⟨⟨j, hjdim⟩, x, hxj, rfl⟩
    exact measure_mono_null hsub (measure_iUnion_null
      (fun j : J => (P j.val).linear_image_null_of_dim_lt_two L j.property))
  refine ⟨isClosed_iUnion_of_finite (fun i => (hcompact i).isClosed),
    measure_iUnion_null hnull, ?_⟩
  intro i hi
  have hsub : L '' ((P i).image ∩ K) ⊆ C ⟨i, hi⟩ :=
    image_mono (fun _ hx => ⟨subset_closure hx.1, hx.2⟩)
  have hclose : closure (L '' ((P i).image ∩ K)) ⊆ C (⟨i, hi⟩ : J) :=
    (hcompact ⟨i, hi⟩).isClosed.closure_subset_iff.mpr hsub
  exact hclose.trans (subset_iUnion C (⟨i, hi⟩ : J))

theorem ranDefinable_stratumCompactProjectionException
    {n : ℕ} {ι : Type} [Fintype ι]
    (P : ι → AnalyticStratificationChart (Fin n → ℝ))
    (hP : ∀ i, RanDefinable (P i).image)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKd : RanDefinable K)
    (L : (Fin n → ℝ) →L[ℝ] Base 2) :
    RanDefinable (stratumCompactProjectionException P K L) := by
  apply Set.definable_iUnion_of_finite
  intro i
  have hS : RanDefinable (closure (P i.val).image ∩ K) := (hP i.val).closure.inter hKd
  have hSc : IsCompact (closure (P i.val).image ∩ K) := hK.inter_left isClosed_closure
  apply ranDefinable_image_on hS
  intro j
  exact ranDefinableOn_of_analyticOnNhd_compact_closure hS hSc.closure
    (fun x _ => analyticAt_pi_iff.mp (L.analyticAt x) j)

end PlanarNikodym
