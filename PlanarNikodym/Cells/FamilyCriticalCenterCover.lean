import PlanarNikodym.Cells.FamilyIntrinsicRankCover
import PlanarNikodym.Cells.IntrinsicRankCriticalCenters

/-! The R3--R4 output for the original analytic family. No boundary
barrier, fiber-cutting certificate or projection-nullity hypothesis is
required from the caller. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.exists_intrinsic_rank_cover_with_critical_exception
    {d : ℕ} (G : Family 2 d) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (S : Set (Fin (d + 2) → ℝ)) (hS : LocallySemianalytic S)
    (hb : Bornology.IsBounded S) (hSW : closure S ⊆ (parameterFrame d) ⁻¹' G.W) :
    ∃ (ι : Type) (_ : Fintype ι)
      (P : ι → IntrinsicRankChart ((parameterFrame d) ⁻¹' G.W)
        G.coordinateFunctionDerivative (parameterCenterDerivative d)),
      (⋃ i, (P i).chart.image) = S ∧
      ∃ E : Set (Fin 2 → ℝ), RanDefinable E ∧ IsCompact E ∧ volume E = 0 ∧
        E = closure ((parameterCenterDerivative d) ''
          (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image)) ∧
        (parameterCenterDerivative d) '' closure
          (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image) ⊆ E ∧
        ∀ i, (P i).centerCritical →
          closure ((parameterCenterDerivative d) '' (P i).chart.image) ⊆ E := by
  obtain ⟨ι, hι, P, hcover⟩ := G.exists_finite_intrinsic_rank_cover ho ha S hS hb hSW
  have hPS (i : ι) : (P i).chart.image ⊆ S := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  exact ⟨ι, hι, P, hcover,
    finite_intrinsic_rank_critical_centers_compact_null P (fun i => hb.subset (hPS i))⟩

theorem Family.exists_intrinsic_rank_ball_cover_with_critical_exception
    {d : ℕ} (G : Family 2 d) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (c : Fin (d + 2) → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ (parameterFrame d) ⁻¹' G.W) :
    ∃ (ι : Type) (_ : Fintype ι)
      (P : ι → IntrinsicRankChart ((parameterFrame d) ⁻¹' G.W)
        G.coordinateFunctionDerivative (parameterCenterDerivative d)),
      (⋃ i, (P i).chart.image) = Metric.ball c r ∧
      ∃ E : Set (Fin 2 → ℝ), RanDefinable E ∧ IsCompact E ∧ volume E = 0 ∧
        E = closure ((parameterCenterDerivative d) ''
          (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image)) ∧
        (parameterCenterDerivative d) '' closure
          (⋃ i : {i // (P i).centerCritical}, (P i.val).chart.image) ⊆ E ∧
        ∀ i, (P i).centerCritical →
          closure ((parameterCenterDerivative d) '' (P i).chart.image) ⊆ E :=
  G.exists_intrinsic_rank_cover_with_critical_exception ho ha (Metric.ball c r)
    (locallySemianalytic_coordinate_ball c r hr) Metric.isBounded_ball hball

end PlanarNikodym
