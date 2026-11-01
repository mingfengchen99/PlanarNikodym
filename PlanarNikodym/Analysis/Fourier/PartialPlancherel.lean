import PlanarNikodym.Analysis.Fourier.PartialFourierRepresentation
import PlanarNikodym.Analysis.Fourier.TimeDataScaling

/-! Plancherel for the actual partial inverse Fourier integral. The compact
frequency amplitude remains in the data, and the inverse time dilation
contributes exactly `r⁻¹` to its squared L² mass. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

/-- A one-dimensional slice of a smooth compact frequency amplitude. -/
def partialFrequencySchwartz (a : Plane → ℂ) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (η : ℝ) : SchwartzMap ℝ ℂ := by
  apply HasCompactSupport.toSchwartzMap
    (f := fun ξ : ℝ => a (ξ, η))
  · apply HasCompactSupport.intro (hc.isCompact.image continuous_fst)
    intro ξ hξ
    exact image_eq_zero_of_notMem_tsupport
      (fun hmem => hξ ⟨(ξ, η), hmem, rfl⟩)
  · exact ha.comp (contDiff_id.prodMk contDiff_const)

@[simp] theorem partialFrequencySchwartz_apply (a : Plane → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (η ξ : ℝ) :
    partialFrequencySchwartz a ha hc η ξ = a (ξ, η) := rfl

/-- The partial data uses exactly Mathlib's inverse Fourier convention,
including the `2π` in the exponential. -/
theorem partialFourierData_eq_fourierInv (a : Plane → ℂ) (r t η : ℝ) :
    partialFourierData a r t η = 𝓕⁻ (fun ξ : ℝ => a (ξ, η)) (r * t) := by
  rw [Real.fourierInv_eq']
  unfold partialFourierData
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [oneDimFourierCharacter, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [mul_comm (a (ξ, η))]
  congr 2
  push_cast
  ring

/-- Squared Plancherel mass of an actual Schwartz inverse Fourier integral. -/
theorem lintegral_enorm_sq_fourierInv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ) :
    (∫⁻ t : E, ‖𝓕⁻ (⇑f) t‖ₑ ^ (2 : ℕ)) = ∫⁻ ξ : E, ‖f ξ‖ₑ ^ (2 : ℕ) := by
  have h := (𝓕⁻ f).integral_norm_sq_fourier
  simp only [FourierTransform.fourier_fourierInv_eq] at h
  have hInv : Integrable (fun t : E => ‖𝓕⁻ f t‖ ^ (2 : ℕ)) :=
    (𝓕⁻ f).memLp 2 |>.integrable_norm_pow (by norm_num)
  have hf : Integrable (fun ξ : E => ‖f ξ‖ ^ (2 : ℕ)) :=
    (f.memLp 2).integrable_norm_pow (by norm_num)
  have hL := ofReal_integral_eq_lintegral_ofReal hInv
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have hR := ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  rw [← h] at hL
  have he := hL.symm.trans hR
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    SchwartzMap.fourierInv_coe] using he

/-- The forward transform has the same squared Plancherel mass. -/
theorem lintegral_enorm_sq_fourier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ) :
    (∫⁻ ξ : E, ‖𝓕 (⇑f) ξ‖ₑ ^ (2 : ℕ)) = ∫⁻ x : E, ‖f x‖ₑ ^ (2 : ℕ) := by
  have h := lintegral_enorm_sq_fourierInv (𝓕 f)
  rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq] at h
  simpa only [SchwartzMap.fourier_coe] using h.symm

/-- One-dimensional partial Plancherel, with no unweighted substitution
for the actual frequency amplitude. -/
theorem lintegral_partialFourierData_sq (a : Plane → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {r : ℝ} (hr : 0 < r) (η : ℝ) :
    (∫⁻ t : ℝ, ‖partialFourierData a r t η‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal r⁻¹ * ∫⁻ ξ : ℝ, ‖a (ξ, η)‖ₑ ^ (2 : ℕ) := by
  let f := partialFrequencySchwartz a ha hc η
  have hF : Measurable (fun t : ℝ => ‖𝓕⁻ (⇑f) t‖ₑ ^ (2 : ℕ)) := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ f).continuous.enorm.measurable.pow_const _
  calc
    _ = ∫⁻ t : ℝ, ‖𝓕⁻ (⇑f) (r * t)‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro t
      rw [partialFourierData_eq_fourierInv]
      rfl
    _ = ∫⁻ t : ℝ, ‖𝓕⁻ (⇑f) t‖ₑ ^ (2 : ℕ)
        ∂Measure.map (fun t : ℝ => r * t) volume :=
      (lintegral_map hF (by fun_prop)).symm
    _ = ENNReal.ofReal r⁻¹ * ∫⁻ t : ℝ, ‖𝓕⁻ (⇑f) t‖ₑ ^ (2 : ℕ) := by
      rw [Real.map_volume_mul_left hr.ne', abs_of_pos (inv_pos.mpr hr),
        lintegral_smul_measure, smul_eq_mul]
    _ = _ := by rw [lintegral_enorm_sq_fourierInv]; rfl

/-- Full two-variable partial Plancherel after Tonelli. -/
theorem lintegral_partialFourierData_plane_sq (a : Plane → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Plane, ‖partialFourierData a r x.1 x.2‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal r⁻¹ * ∫⁻ ξ : Plane, ‖a ξ‖ₑ ^ (2 : ℕ) := by
  rw [Measure.volume_eq_prod,
    lintegral_prod_symm _ ((stronglyMeasurable_partialFourierData ha.continuous r).enorm.pow_const _).aemeasurable]
  simp_rw [lintegral_partialFourierData_sq a ha hc hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_prod_symm _ (ha.continuous.enorm.measurable.pow_const _).aemeasurable]

/-- The square-root form of the exact two-variable partial Plancherel
identity displays the `r⁻¹ᐟ²` L² factor. -/
theorem eLpNorm_partialFourierData_two (a : Plane → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x : Plane => partialFourierData a r x.1 x.2) 2 volume =
      ENNReal.ofReal r⁻¹ ^ (1 / (2 : ℝ)) * eLpNorm a 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_partialFourierData_plane_sq a ha hc hr,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ 1 / (2 : ℝ))]

end PlanarNikodym
