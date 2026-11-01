import PlanarNikodym.Cells.FiniteSemianalyticFiberCutting
import PlanarNikodym.Cells.LowDimensionalProjectionContainer

/-! D-R4: same-projection semianalytic sources and compact definable null
center exceptions for the actual critical members of an intrinsic-rank
cover. High source dimension is allowed throughout. -/
noncomputable section
open Set Module MeasureTheory
namespace PlanarNikodym

theorem AnalyticStratificationChart.critical_projection_compact_null
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (hQ : LocallySemianalytic Q.image) (hb : Bornology.IsBounded Q.image)
    (K : Set (Fin n → ℝ)) (hQK : Q.image ⊆ K)
    (hreg : RegularStratumEquations K Q.image Q.dim)
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (hr : ∀ q ∈ Q.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range ≤ 1) :
    RanDefinable (closure (L '' Q.image)) ∧ IsCompact (closure (L '' Q.image)) ∧
      dimH (closure (L '' Q.image)) ≤ 1 ∧ volume (closure (L '' Q.image)) = 0 := by
  obtain ⟨B, _, hB, hbB, hdB, he⟩ := Q.exists_semianalytic_fiber_cut hQ hb K hQK hreg L hr
  obtain ⟨hc, hdef, hd, hn, hcl⟩ := hB.low_dimensional_projection_container hbB hdB L
  rw [he] at hcl
  rw [hcl]
  exact ⟨hdef, hc, hd, hn⟩

def IntrinsicRankChart.centerCritical {n : ℕ} {X : Type}
    {O : Set (Fin n → ℝ)} {A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} (P : IntrinsicRankChart O A L) : Prop :=
  ∃ q ∈ P.chart.source,
    finrank ℝ (L.toLinearMap.comp (fderiv ℝ P.chart.map q).toLinearMap).range ≤ 1

theorem IntrinsicRankChart.center_rank_le_one_of_critical
    {n : ℕ} {X : Type} {O : Set (Fin n → ℝ)}
    {A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} (P : IntrinsicRankChart O A L)
    (h : P.centerCritical) :
    ∀ q ∈ P.chart.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ P.chart.map q).toLinearMap).range ≤ 1 := by
  obtain ⟨r, _, _, hr⟩ := P.ranks
  obtain ⟨x, hx, hxr⟩ := h
  intro q hq
  rw [(hr q hq).1, ← (hr x hx).1]
  exact hxr

theorem finite_intrinsic_rank_critical_fiber_cut
    {n : ℕ} {X : Type} {O : Set (Fin n → ℝ)}
    {A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {ι : Type} [Fintype ι]
    (P : ι → IntrinsicRankChart O A L)
    (hb : ∀ i, Bornology.IsBounded (P i).chart.image) :
    ∃ B : Set (Fin n → ℝ), B ⊆ ⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image ∧
      LocallySemianalytic B ∧ Bornology.IsBounded B ∧ dimH B ≤ 1 ∧
      L '' B = L '' (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image) := by
  classical
  apply HasSemianalyticFiberCut.finite_union
  intro i
  exact (P i.val).chart.exists_semianalytic_fiber_cut (P i.val).semianalytic (hb i.val)
    (closure (P i.val).window) ((P i.val).image_window.trans subset_closure)
    (P i.val).regular L ((P i.val).center_rank_le_one_of_critical i.property)

theorem finite_intrinsic_rank_critical_centers_compact_null
    {n : ℕ} {X : Type} {O : Set (Fin n → ℝ)}
    {A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {ι : Type} [Fintype ι]
    (P : ι → IntrinsicRankChart O A L)
    (hb : ∀ i, Bornology.IsBounded (P i).chart.image) :
    ∃ E : Set (Fin 2 → ℝ), RanDefinable E ∧ IsCompact E ∧ volume E = 0 ∧
      E = closure (L '' (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image)) ∧
      L '' closure (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image) ⊆ E ∧
      ∀ i, (P i).centerCritical → closure (L '' (P i).chart.image) ⊆ E := by
  classical
  obtain ⟨B, _, hB, hbB, hdB, he⟩ := finite_intrinsic_rank_critical_fiber_cut P hb
  obtain ⟨E, hdef, hc, hn, heE⟩ := hB.closed_null_container_of_same_projection hbB hdB L he
  refine ⟨E, hdef, hc, hn, heE.symm, ?_, ?_⟩
  · rw [← heE]
    exact image_closure_subset_closure_image L.continuous
  intro i hi
  rw [← heE]
  exact closure_mono (image_mono (fun x hx => mem_iUnion.mpr
    ⟨(⟨i, hi⟩ : {i // (P i).centerCritical}), hx⟩))

theorem finite_intrinsic_rank_critical_source_closure_projection_null
    {n : ℕ} {X : Type} {O : Set (Fin n → ℝ)}
    {A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {ι : Type} [Fintype ι]
    (P : ι → IntrinsicRankChart O A L)
    (hb : ∀ i, Bornology.IsBounded (P i).chart.image) :
    volume (L '' closure (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image)) = 0 := by
  obtain ⟨_, _, _, hn, _, hsub, _⟩ := finite_intrinsic_rank_critical_centers_compact_null P hb
  exact measure_mono_null hsub hn

end PlanarNikodym
