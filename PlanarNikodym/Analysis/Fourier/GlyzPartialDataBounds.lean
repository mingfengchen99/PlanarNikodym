import PlanarNikodym.Analysis.Fourier.PartialDataRawExtension

/-! Actual radial support and L1 mass of compact-time partial data. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem timeRestrictedPartialData_radial_support {T J : Set ℝ} {m : Plane → ℝ}
    (hm : Prod.snd '' tsupport m ⊆ J) (f : Plane → ℂ) (r : ℝ) :
    Function.support (timeRestrictedPartialData T m f r) ⊆ {y | y.2 ∈ J} := by
  intro y hy
  by_contra hn
  have hv : y.2 ∉ Prod.snd '' tsupport m := fun h => hn (hm h)
  have hz := weightedPartialFourierData_eq_zero_of_vertical (f := f) r y.1 y.2 hv
  apply hy
  simp only [timeRestrictedPartialData]
  by_cases ht : y ∈ T ×ˢ (univ : Set ℝ)
  · rw [indicator_of_mem ht, hz]
  · exact indicator_of_notMem ht _

theorem integral_norm_timeRestrictedPartialData_le {T : Set ℝ} (hT : MeasurableSet T)
    (hTv : volume T ≠ (∞ : ℝ≥0∞)) {m : Plane → ℝ} (hm : Continuous m)
    (hmc : HasCompactSupport m) {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    (∫ y, ‖timeRestrictedPartialData T m f r y‖) ≤
      (volume T).toReal * lpNorm m 1 volume * lpNorm f 1 volume := by
  have hd := integrable_timeRestrictedPartialData hT hTv hm hmc hf r
  have hfin : volume T * eLpNorm m 1 volume * eLpNorm f 1 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hTv
      (hm.memLp_of_hasCompactSupport hmc (p := 1)).eLpNorm_ne_top)
      (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
  have hh := ENNReal.toReal_mono hfin (lintegral_timeRestrictedPartialData_le hT hm hf r)
  rw [← eLpNorm_one_eq_lintegral_enorm,
    toReal_eLpNorm hd.aestronglyMeasurable, lpNorm_one_eq_integral_norm hd.aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    toReal_eLpNorm hm.aestronglyMeasurable, toReal_eLpNorm hf.aestronglyMeasurable] at hh
  exact hh

end PlanarNikodym
