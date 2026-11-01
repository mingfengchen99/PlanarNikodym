import PlanarNikodym.Cells.IntrinsicRankCriticalCenters
import PlanarNikodym.Geometry.ContinuousImageComponentSources

/-! A low-dimensional semianalytic source for every actual connected
component of the entire closed critical-center exception. Both the closed
exception and all its components have finitely many definable components;
no general R_an component theorem is assumed. -/
noncomputable section
open Set Module MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem finite_intrinsic_rank_critical_component_sources
    {n : ℕ} {X : Type} {O : Set (Fin n → ℝ)}
    {A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)} {ι : Type} [Fintype ι]
    (P : ι → IntrinsicRankChart O A L)
    (hb : ∀ i, Bornology.IsBounded (P i).chart.image) :
    ∃ B : Set (Fin n → ℝ), LocallySemianalytic B ∧ Bornology.IsBounded B ∧
      dimH B ≤ 1 ∧
      L '' closure B = closure (L '' (⋃ i : {i // (P i).centerCritical},
        (P i.val).chart.image)) ∧
      IsCompact (L '' closure B) ∧ volume (L '' closure B) = 0 ∧
      (componentDomains (L '' closure B)).Finite ∧
      ∀ y, RanDefinable (_root_.connectedComponentIn (L '' closure B) y) ∧
        ∃ C : Set (Fin n → ℝ), C ⊆ closure B ∧ LocallySemianalytic C ∧
          IsCompact C ∧ dimH C ≤ 1 ∧
          L '' C = _root_.connectedComponentIn (L '' closure B) y := by
  classical
  obtain ⟨B, _, hB, hbB, hdB, he⟩ := finite_intrinsic_rank_critical_fiber_cut P hb
  obtain ⟨hc, _, _, hn, hcl⟩ := hB.low_dimensional_projection_container hbB hdB L
  have hBc := hB.closure
  have hBd : dimH (closure B) ≤ 1 := by rwa [hB.dimH_closure]
  have hcomp := hBc.finite_definable_analytic_image_components hbB.closure L
    (fun x _ => L.analyticAt x)
  refine ⟨B, hB, hbB, hdB, ?_, hc, hn, hcomp.1, ?_⟩
  · rw [← hcl, he]
  intro y
  refine ⟨hcomp.2 y, ?_⟩
  obtain ⟨C, hCB, hC, hbC, himage, hclosure⟩ :=
    hBc.exists_component_image_source_with_closure hbB.closure L L.continuous.continuousOn y
  have hclosed : IsClosed (_root_.connectedComponentIn (L '' closure B) y) := by
    by_cases hy : y ∈ L '' closure B
    · apply isClosed_of_closure_subset
      exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hy))
        (closure_minimal (connectedComponentIn_subset _ _) hc.isClosed)
    · rw [connectedComponentIn_eq_empty hy]
      exact isClosed_empty
  refine ⟨closure C, closure_minimal hCB isClosed_closure, hC.closure,
    hbC.isCompact_closure, ?_, ?_⟩
  · exact (dimH_mono (closure_minimal hCB isClosed_closure)).trans hBd
  · rwa [hclosed.closure_eq] at hclosure

end PlanarNikodym
