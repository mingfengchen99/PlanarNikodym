import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Exact scaling of the partial-Fourier input data. This is the time
Jacobian needed on the input side of the extension reduction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

def timeDataRescaling (c δ : ℝ) (x : Plane) : Plane := (c + δ * x.1, x.2)

theorem map_timeDataRescaling_volume (c : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    Measure.map (timeDataRescaling c δ) volume = ENNReal.ofReal |δ⁻¹| • (volume : Measure Plane) := by
  have htime : Measure.map (fun t : ℝ => c + δ * t) volume =
      ENNReal.ofReal |δ⁻¹| • (volume : Measure ℝ) := by
    have he : (fun t : ℝ => c + δ * t) = (fun t => c + t) ∘ (fun t => δ * t) := rfl
    rw [he, ← Measure.map_map (show Measurable (fun t : ℝ => c + t) by fun_prop)
      (show Measurable (fun t : ℝ => δ * t) by fun_prop), Real.map_volume_mul_left hδ,
      Measure.map_smul, map_add_left_eq_self]
  change Measure.map (Prod.map (fun t : ℝ => c + δ * t) id) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) measurable_id,
    htime, Measure.map_id, Measure.prod_smul_left]
  rfl

theorem eLpNorm_timeDataRescaling {h : Plane → ℂ} (hh : StronglyMeasurable h)
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    eLpNorm (fun x : Plane => h (c + δ * x.1, x.2)) p volume =
      ENNReal.ofReal δ⁻¹ ^ (1 / p).toReal * eLpNorm h p volume := by
  have hA : Measurable (timeDataRescaling c δ) := by unfold timeDataRescaling; fun_prop
  rw [show (fun x => h (c + δ * x.1, x.2)) = h ∘ timeDataRescaling c δ from rfl,
    ← eLpNorm_map_measure hh.aestronglyMeasurable hA.aemeasurable,
    map_timeDataRescaling_volume c hδ.ne', eLpNorm_smul_measure_of_ne_top hp]
  rw [abs_of_pos (inv_pos.mpr hδ)]
  rfl

end PlanarNikodym
