import PlanarNikodym.Analysis.Fourier.TimeLocalizedIntegrability
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! The original compact-frequency partial Fourier data has a uniform
L1 bound on every fixed finite time window. A compact physical input
then converts this bound to the original input's Lp norm. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym
set_option backward.isDefEq.respectTransparency false

theorem enorm_planeFourierIntegral_le_L1 (f : Plane → ℂ) (ξ : Plane) :
    ‖planeFourierIntegral f ξ‖ₑ ≤ eLpNorm f 1 volume := by
  calc
    _ ≤ ∫⁻ y, ‖f y * planeFourierCharacter (-y) ξ‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = _ := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      apply lintegral_congr
      intro y
      rw [enorm_mul, ← ofReal_norm (planeFourierCharacter (-y) ξ),
        norm_planeFourierCharacter, ENNReal.ofReal_one, mul_one]

theorem enorm_weightedPartialFourierData_le_L1 {m : Plane → ℝ}
    (hm : Continuous m) (f : Plane → ℂ) (r t η : ℝ) :
    ‖weightedPartialFourierData m f r t η‖ₑ ≤
      (∫⁻ ξ : ℝ, ‖m (ξ, η)‖ₑ) * eLpNorm f 1 volume := by
  calc
    _ ≤ ∫⁻ ξ : ℝ, ‖((m (ξ, η) : ℝ) : ℂ) *
        planeFourierIntegral f (r • (ξ, η)) * oneDimFourierCharacter r t ξ‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ ξ : ℝ, ‖m (ξ, η)‖ₑ * eLpNorm f 1 volume := by
      apply lintegral_mono
      intro ξ
      dsimp only
      rw [enorm_mul, enorm_mul,
        ← ofReal_norm (oneDimFourierCharacter r t ξ),
        norm_oneDimFourierCharacter, ENNReal.ofReal_one, mul_one,
        ← ofReal_norm ((m (ξ, η) : ℝ) : ℂ), Complex.norm_real, ofReal_norm]
      exact mul_le_mul_right (enorm_planeFourierIntegral_le_L1 f _) _
    _ = _ := lintegral_mul_const _
      (((hm.comp (continuous_id.prodMk continuous_const)).enorm).measurable)

def timeRestrictedPartialData (T : Set ℝ) (m : Plane → ℝ)
    (f : Plane → ℂ) (r : ℝ) : Plane → ℂ :=
  (T ×ˢ univ).indicator (fun y => weightedPartialFourierData m f r y.1 y.2)

theorem lintegral_timeRestrictedPartialData_le {T : Set ℝ} (hT : MeasurableSet T)
    {m : Plane → ℝ} (hm : Continuous m) {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    (∫⁻ y, ‖timeRestrictedPartialData T m f r y‖ₑ) ≤
      volume T * eLpNorm m 1 volume * eLpNorm f 1 volume := by
  have hdata := stronglyMeasurable_partialFourierData
    (weighted_scaledFourierData_continuous hm hf r) r
  have hmeas : Measurable (fun y : Plane => ‖timeRestrictedPartialData T m f r y‖ₑ) :=
    (hdata.measurable.indicator (hT.prod MeasurableSet.univ)).enorm
  conv_lhs => rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  have hbound (t : ℝ) :
      (∫⁻ η : ℝ, ‖timeRestrictedPartialData T m f r (t, η)‖ₑ) ≤
        T.indicator (fun _ => eLpNorm m 1 volume * eLpNorm f 1 volume) t := by
    by_cases ht : t ∈ T
    · rw [indicator_of_mem ht]
      have hi : ∀ η : ℝ, timeRestrictedPartialData T m f r (t, η) =
          weightedPartialFourierData m f r t η := by
        intro η
        exact indicator_of_mem (show (t, η) ∈ T ×ˢ (univ : Set ℝ) from ⟨ht, mem_univ _⟩) _
      simp_rw [hi]
      calc
        _ ≤ ∫⁻ η : ℝ, (∫⁻ ξ : ℝ, ‖m (ξ, η)‖ₑ) * eLpNorm f 1 volume :=
          lintegral_mono (enorm_weightedPartialFourierData_le_L1 hm f r t)
        _ = (∫⁻ η : ℝ, ∫⁻ ξ : ℝ, ‖m (ξ, η)‖ₑ) * eLpNorm f 1 volume :=
          lintegral_mul_const _ hm.enorm.measurable.lintegral_prod_left
        _ = _ := by
          rw [← lintegral_prod_symm _ hm.enorm.measurable.aemeasurable]
          simp only [eLpNorm_one_eq_lintegral_enorm, Measure.volume_eq_prod]
    · have hi : ∀ η : ℝ, timeRestrictedPartialData T m f r (t, η) = 0 := by
        intro η
        exact indicator_of_notMem (fun h => ht h.1) _
      simp only [hi, enorm_zero, lintegral_zero, indicator_of_notMem ht, le_refl]
  calc
    _ ≤ ∫⁻ t, T.indicator (fun _ => eLpNorm m 1 volume * eLpNorm f 1 volume) t :=
      lintegral_mono hbound
    _ = _ := by rw [lintegral_indicator_const hT]; ring

theorem integrable_timeRestrictedPartialData {T : Set ℝ} (hT : MeasurableSet T)
    (hTv : volume T ≠ (∞ : ℝ≥0∞)) {m : Plane → ℝ} (hm : Continuous m)
    (hmc : HasCompactSupport m) {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    Integrable (timeRestrictedPartialData T m f r) := by
  refine ⟨(stronglyMeasurable_partialFourierData
    (weighted_scaledFourierData_continuous hm hf r) r).aestronglyMeasurable.indicator
      (hT.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply (lintegral_timeRestrictedPartialData_le hT hm hf r).trans_lt
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hTv.lt_top
      (hm.memLp_of_hasCompactSupport hmc (p := 1)).eLpNorm_lt_top)
    (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top

theorem eLpNorm_one_indicator_le_compact_volume {S : Set Plane}
    (hS : MeasurableSet S)
    {f : Plane → ℂ} (hf : Integrable f) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (S.indicator f) 1 volume ≤
      eLpNorm f p volume * (volume S) ^ (1 - 1 / p.toReal) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hS]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict S) (f := f) (p := 1) (q := p) hp hf.aestronglyMeasurable.restrict
  simpa only [ENNReal.toReal_one, div_one, one_div, Measure.restrict_apply_univ] using
    h.trans (mul_le_mul_left (eLpNorm_mono_measure _ Measure.restrict_le_self) _)

end PlanarNikodym
