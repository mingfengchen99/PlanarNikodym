import PlanarNikodym.Cells.RankZeroFiberCutting
import PlanarNikodym.Geometry.RegularSubstratumTangent

/-! The construction target and finite union operation for fiber cutting.
The existence theorem is proved by source-dimension induction separately. -/
noncomputable section
open Set
open scoped ENNReal NNReal
namespace PlanarNikodym

def HasSemianalyticFiberCut {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ B : Set (Fin n → ℝ), B ⊆ A ∧ LocallySemianalytic B ∧
    Bornology.IsBounded B ∧ dimH B ≤ 1 ∧ L '' B = L '' A

theorem HasSemianalyticFiberCut.of_low_dimension
    {n : ℕ} {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {A : Set (Fin n → ℝ)}
    (hA : LocallySemianalytic A) (hb : Bornology.IsBounded A) (hd : dimH A ≤ 1) :
    HasSemianalyticFiberCut L A := ⟨A, Subset.rfl, hA, hb, hd, rfl⟩

theorem HasSemianalyticFiberCut.finite_union
    {n : ℕ} {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {ι : Type} [Fintype ι]
    (A : ι → Set (Fin n → ℝ)) (h : ∀ i, HasSemianalyticFiberCut L (A i)) :
    HasSemianalyticFiberCut L (⋃ i, A i) := by
  classical
  choose B hBA hsemi hb hd he using h
  refine ⟨⋃ i, B i, iUnion_mono hBA, LocallySemianalytic.iUnion _ hsemi,
    Bornology.isBounded_iUnion.mpr hb, ?_, ?_⟩
  · rw [dimH_iUnion]
    exact iSup_le hd
  · rw [image_iUnion, image_iUnion]
    simp_rw [he]

theorem HasSemianalyticFiberCut.of_subset_same_projection
    {n : ℕ} {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {A C : Set (Fin n → ℝ)}
    (h : HasSemianalyticFiberCut L C) (hCA : C ⊆ A) (he : L '' C = L '' A) :
    HasSemianalyticFiberCut L A := by
  obtain ⟨B, hBC, hB, hb, hd, hL⟩ := h
  exact ⟨B, hBC.trans hCA, hB, hb, hd, hL.trans he⟩

theorem HasSemianalyticFiberCut.of_finite_cover_enlargements
    {n : ℕ} {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {A : Set (Fin n → ℝ)}
    {ι : Type} [Fintype ι] (S C : ι → Set (Fin n → ℝ))
    (hcover : (⋃ i, S i) = A) (hCA : ∀ i, C i ⊆ A)
    (hproj : ∀ i, L '' S i ⊆ L '' C i) (hcut : ∀ i, HasSemianalyticFiberCut L (C i)) :
    HasSemianalyticFiberCut L A := by
  apply (HasSemianalyticFiberCut.finite_union C hcut).of_subset_same_projection
    (iUnion_subset hCA)
  apply Subset.antisymm (image_mono (iUnion_subset hCA))
  rw [← hcover, image_iUnion, image_iUnion]
  exact iUnion_mono hproj

theorem AnalyticStratificationChart.fiber_cut_of_rank_zero
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (hr : ∀ q ∈ Q.source,
      Module.finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = 0) :
    HasSemianalyticFiberCut L Q.image := by
  obtain ⟨B, hBQ, hB, hb, hd, he⟩ := Q.exists_semianalytic_rank_zero_fiber_cut L hr
  exact ⟨B, hBQ, hB, hb, hd.le.trans (by norm_num), he⟩

end PlanarNikodym
