import PlanarNikodym.Cells.SemianalyticClosureHausdorff
import PlanarNikodym.Tame.DefinableContinuousImageComponents
import PlanarNikodym.Geometry.AnalyticStratificationSemianalyticClosure
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! The final compactification step of fiber cutting. Closure control
comes from the semianalytic source, independently of any extension of its
chart parametrizations to their boundary. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem LocallySemianalytic.low_dimensional_projection_container
    {n : ℕ} {B : Set (Fin n → ℝ)} (hB : LocallySemianalytic B)
    (hb : Bornology.IsBounded B) (hd : dimH B ≤ 1)
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) :
    IsCompact (L '' _root_.closure B) ∧ RanDefinable (L '' _root_.closure B) ∧
      dimH (L '' _root_.closure B) ≤ 1 ∧ volume (L '' _root_.closure B) = 0 ∧
      _root_.closure (L '' B) = L '' _root_.closure B := by
  have hcomp := hb.isCompact_closure.image L.continuous
  have hsemi : LocallySemianalytic (_root_.closure B) := hB.closure
  have hdef := hsemi.ranDefinable_of_bounded hb.closure
  have hdim : dimH (L '' _root_.closure B) ≤ 1 := calc
    _ ≤ dimH (_root_.closure B) := L.lipschitz.dimH_image_le _
    _ = dimH B := hB.dimH_closure
    _ ≤ 1 := hd
  refine ⟨hcomp, ?_, hdim, ?_, ?_⟩
  · apply ranDefinable_image_on hdef
    intro j
    exact ranDefinableOn_of_analyticOnNhd_compact_closure hdef hb.isCompact_closure.closure
      (fun x _ => analyticAt_pi_iff.mp (L.analyticAt x) j)
  · have hz := hausdorffMeasure_of_dimH_lt (d := (2 : ℝ≥0))
      (hdim.trans_lt (by norm_num : (1 : ℝ≥0∞) < 2))
    have he := hausdorffMeasure_pi_real (ι := Fin 2)
    norm_num only [Fintype.card_fin] at he
    norm_num only [NNReal.coe_ofNat] at hz
    rw [he] at hz
    exact hz
  · apply Subset.antisymm (hcomp.isClosed.closure_subset_iff.mpr (image_mono subset_closure))
    exact image_closure_subset_closure_image L.continuous

theorem LocallySemianalytic.closed_null_container_of_same_projection
    {n : ℕ} {A B : Set (Fin n → ℝ)} (hB : LocallySemianalytic B)
    (hb : Bornology.IsBounded B) (hd : dimH B ≤ 1)
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) (he : L '' B = L '' A) :
    ∃ E : Set (Fin 2 → ℝ), RanDefinable E ∧ IsCompact E ∧
      volume E = 0 ∧ _root_.closure (L '' A) = E := by
  obtain ⟨hc, hdef, _, hn, heq⟩ := hB.low_dimensional_projection_container hb hd L
  exact ⟨L '' _root_.closure B, hdef, hc, hn, he ▸ heq⟩

end PlanarNikodym
