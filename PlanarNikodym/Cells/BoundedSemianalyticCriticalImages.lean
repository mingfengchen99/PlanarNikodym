import PlanarNikodym.Tame.DefinableContinuousImageComponents
import PlanarNikodym.Cells.CompactAnalyticCriticalCenters

/-! A real closed, definable and null center exception from a bounded
semianalytic parameter set and its actual analytic critical map. The compact
container and the open analytic domain are constructed from the source. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem bounded_analytic_critical_image_closure_null {n : ℕ}
    (f : Aux n → Base 2) {S : Set (Aux n)} (hb : Bornology.IsBounded S)
    (ha : AnalyticOnNhd ℝ f (closure S))
    (hc : ∀ x ∈ S, ¬ Function.Surjective (fderiv ℝ f x)) :
    volume (closure (f '' S)) = 0 := by
  let U : Set (Aux n) := {x | AnalyticAt ℝ f x}
  apply closure_analytic_critical_center_image_null f
    (U := U) (K := closure S) (S := S) (isOpen_analyticAt ℝ f)
    (fun _ hx => hx) hb.isCompact_closure (fun x hx => ha x hx) subset_closure hc

theorem LocallySemianalytic.critical_image_closure_definable_closed_null {n : ℕ}
    {S : Set (Aux n)} (hS : LocallySemianalytic S) (hb : Bornology.IsBounded S)
    (f : Aux n → Base 2) (ha : AnalyticOnNhd ℝ f (closure S))
    (hc : ∀ x ∈ S, ¬ Function.Surjective (fderiv ℝ f x)) :
    RanDefinable (closure (f '' S)) ∧ IsClosed (closure (f '' S)) ∧
      volume (closure (f '' S)) = 0 := by
  have hd : RanDefinable S := hS.ranDefinable_of_bounded hb
  have hfd (i : Fin 2) : RanDefinableOn (fun x => f x i) S :=
    ranDefinableOn_of_analyticOnNhd_compact_closure hd hb.isCompact_closure
      (fun x hx => analyticAt_pi_iff.mp (ha x hx) i)
  exact ⟨RanDefinable.closure (ranDefinable_image_on hd hfd), isClosed_closure,
    bounded_analytic_critical_image_closure_null f hb ha hc⟩

end PlanarNikodym
