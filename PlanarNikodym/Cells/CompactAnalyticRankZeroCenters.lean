import PlanarNikodym.Geometry.AnalyticCriticalValues
import PlanarNikodym.Cells.CompactCriticalCenters

/-! Closed null zero-rank center images for arbitrary source dimension.
Nullity is proved from the analytic critical-value theorem, rather than
from an assumed null image or an invalid passage to a null-set closure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem compact_analytic_rank_zero_center_image_closed_null {n : ℕ}
    (f : Aux n → Base 2) {U K : Set (Aux n)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IsClosed (f '' {x | x ∈ K ∧ fderiv ℝ f x = 0}) ∧
      volume (f '' {x | x ∈ K ∧ fderiv ℝ f x = 0}) = 0 := by
  have hdc : ContinuousOn (fderiv ℝ f) K := fun x hx =>
    ((ha x (hKU hx)).contDiffAt (n := 1)).continuousAt_fderiv
      (by norm_num) |>.continuousWithinAt
  have hSc : IsClosed {x | x ∈ K ∧ fderiv ℝ f x = 0} :=
    hdc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  have hS : IsCompact {x | x ∈ K ∧ fderiv ℝ f x = 0} :=
    hK.of_isClosed_subset hSc (fun _ hx => hx.1)
  refine ⟨(hS.image_of_continuousOn
    (fun x hx => (ha x (hKU hx.1)).continuousAt.continuousWithinAt)).isClosed, ?_⟩
  have hc := analytic_zero_differential_image_countable f ho ha
  have hs : {x | x ∈ K ∧ fderiv ℝ f x = 0} ⊆
      {x | x ∈ U ∧ fderiv ℝ f x = 0} := fun x hx => ⟨hKU hx.1, hx.2⟩
  exact (hc.mono (image_mono hs)).measure_zero volume

theorem closure_analytic_rank_zero_center_image_null {n : ℕ}
    (f : Aux n → Base 2) {U K S : Set (Aux n)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hSK : S ⊆ K)
    (hz : ∀ x ∈ S, fderiv ℝ f x = 0) :
    volume (closure (f '' S)) = 0 := by
  obtain ⟨hc, hn⟩ :=
    compact_analytic_rank_zero_center_image_closed_null f ho ha hK hKU
  exact measure_mono_null (hc.closure_subset_iff.mpr
    (image_mono (fun x hx => ⟨hSK hx, hz x hx⟩))) hn

end PlanarNikodym
