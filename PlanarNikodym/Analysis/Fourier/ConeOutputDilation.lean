import PlanarNikodym.Analysis.Fourier.LinearConeL2

/-! Exact output Jacobian for the degree-one time-slice phase in unscaled
jet coordinates. Keeping the amplitude in these fixed coordinates avoids
frequency-dependent support constants in its Fourier expansion. -/
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

def coneOutputDilation (δ : ℝ) (w : Plane) : Plane := (w.1, δ * w.2)

theorem map_coneOutputDilation_volume {δ : ℝ} (hδ : δ ≠ 0) :
    Measure.map (coneOutputDilation δ) volume =
      ENNReal.ofReal |δ⁻¹| • (volume : Measure Plane) := by
  change Measure.map (Prod.map id (fun t : ℝ => δ * t)) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume measurable_id (by fun_prop),
    Measure.map_id, Real.map_volume_mul_left hδ, Measure.prod_smul_right]
  rfl

theorem eLpNorm_coneOutputDilation {F : Plane → ℂ} (hF : StronglyMeasurable F)
    {δ : ℝ} (hδ : 0 < δ) (p : ℝ≥0∞) (hp : p ≠ (∞ : ℝ≥0∞)) :
    eLpNorm (fun w : Plane => F (coneOutputDilation δ w)) p volume =
      ENNReal.ofReal δ⁻¹ ^ (1 / p).toReal * eLpNorm F p volume := by
  have hD : Measurable (coneOutputDilation δ) := by unfold coneOutputDilation; fun_prop
  rw [show (fun w => F (coneOutputDilation δ w)) = F ∘ coneOutputDilation δ from rfl,
    ← eLpNorm_map_measure hF.aestronglyMeasurable hD.aemeasurable,
    map_coneOutputDilation_volume hδ.ne', eLpNorm_smul_measure_of_ne_top hp]
  rw [abs_of_pos (inv_pos.mpr hδ)]
  rfl

/-- The exact fixed-coordinate output factor `δ⁻¹ᐟ²` accompanies the
true `r⁻¹` cone estimate, without changing the input or its support. -/
theorem eLpNorm_linearConeExtension_dilated_two_le (h : Plane → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {a r δ : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    eLpNorm (fun w : Plane => linearConeExtension h r (coneOutputDilation δ w)) 2 volume ≤
      ENNReal.ofReal δ⁻¹ ^ (1 / (2 : ℝ)) *
        (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) * eLpNorm h 2 volume) := by
  rw [eLpNorm_coneOutputDilation
    (continuous_linearConeExtension h hh hc ha hgap r).stronglyMeasurable hδ 2
    (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  exact mul_le_mul_right (eLpNorm_linearConeExtension_two_le h hh hc ha hr hgap) _

end PlanarNikodym
