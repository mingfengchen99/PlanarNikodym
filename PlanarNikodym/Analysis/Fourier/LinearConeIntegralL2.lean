import PlanarNikodym.Analysis.Fourier.LinearConeL2
import PlanarNikodym.Analysis.Fourier.PlaneIntegralPlancherel
import PlanarNikodym.Analysis.Fourier.ConeOutputDilation

/-! The actual cone extension on general measurable L¹∩L² inputs.
Its inverse Fourier representation, continuity and L² bound hold for the
original integrals, with no additional smoothness or operator assumption. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem linearConeExtension_eq_inverseFourierIntegral (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (r : ℝ) (w : Plane) :
    linearConeExtension h r w = planeInverseFourierIntegral (coneFrequencyData h) (r • w) := by
  have hki : Integrable (fun ξ : Plane =>
      coneFrequencyData h ξ * planeFourierCharacter (r • w) ξ) :=
    (integrable_coneFrequencyData hh h1).mul_bdd (c := 1)
      (continuous_planeFourierCharacter.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => by simp))
  rw [planeInverseFourierIntegral, Measure.volume_eq_prod, integral_prod _ hki]
  unfold linearConeExtension
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with η hη
  exact (integral_coneFrequencyData_slice h (planeFourierCharacter (r • w)) hη).symm

theorem continuous_linearConeExtension_of_integrable (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (r : ℝ) :
    Continuous (linearConeExtension h r) := by
  have he : linearConeExtension h r =
      fun w => planeInverseFourierIntegral (coneFrequencyData h) (r • w) :=
    funext (linearConeExtension_eq_inverseFourierIntegral h hh h1 r)
  rw [he]
  exact (continuous_planeInverseFourierIntegral (integrable_coneFrequencyData hh h1)).comp
    (continuous_const.smul continuous_id)

/-- Exact squared norm identity for the actual L¹∩L² cone integral. -/
theorem lintegral_linearConeExtension_sq_of_integrable (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ w : Plane, ‖linearConeExtension h r w‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ENNReal.ofReal |x.2|⁻¹ * ‖h x‖ₑ ^ (2 : ℕ) := by
  simp_rw [linearConeExtension_eq_inverseFourierIntegral h hh h1 r]
  rw [lintegral_scaled_planeInverseFourierIntegral_sq (integrable_coneFrequencyData hh h1)
    (memLp_coneFrequencyData_two hh h2 ha hgap) hr, lintegral_coneFrequencyData_sq hh]

/-- The genuine L¹∩L² cone bound with `r⁻²` squared decay. -/
theorem lintegral_linearConeExtension_sq_le_of_integrable (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ w : Plane, ‖linearConeExtension h r w‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  simp_rw [linearConeExtension_eq_inverseFourierIntegral h hh h1 r]
  rw [lintegral_scaled_planeInverseFourierIntegral_sq (integrable_coneFrequencyData hh h1)
    (memLp_coneFrequencyData_two hh h2 ha hgap) hr]
  calc
    _ ≤ ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        (ENNReal.ofReal a⁻¹ * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) :=
      mul_le_mul_right (lintegral_coneFrequencyData_sq_le hh ha hgap) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm (r⁻¹ ^ (2 : ℕ))]

theorem eLpNorm_linearConeExtension_two_le_of_integrable (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    eLpNorm (linearConeExtension h r) 2 volume ≤
      ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) * eLpNorm h 2 volume := by
  have he (g : Plane → ℂ) : eLpNorm g 2 volume =
      (∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (f := g) (μ := volume)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
  rw [he, he]
  calc
    _ ≤ (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow (lintegral_linearConeExtension_sq_le_of_integrable h hh h1 h2 ha hr hgap)
        (by norm_num : 0 ≤ 1 / (2 : ℝ))
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ 1 / (2 : ℝ))

/-- The fixed output-coordinate Jacobian on general input data. -/
theorem lintegral_linearConeExtension_dilated_sq_le_of_integrable (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume) {a r δ : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ w : Plane, ‖linearConeExtension h r (coneOutputDilation δ w)‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal δ⁻¹ * (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) := by
  have hF : Measurable (fun w : Plane => ‖linearConeExtension h r w‖ₑ ^ (2 : ℕ)) :=
    (continuous_linearConeExtension_of_integrable h hh h1 r).enorm.measurable.pow_const _
  rw [← lintegral_map hF (show Measurable (coneOutputDilation δ) by
    unfold coneOutputDilation; fun_prop), map_coneOutputDilation_volume hδ.ne',
    abs_of_pos (inv_pos.mpr hδ), lintegral_smul_measure, smul_eq_mul]
  exact mul_le_mul_right (lintegral_linearConeExtension_sq_le_of_integrable h hh h1 h2 ha hr hgap) _

end PlanarNikodym
