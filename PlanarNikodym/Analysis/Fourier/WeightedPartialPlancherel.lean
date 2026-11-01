import PlanarNikodym.Analysis.Fourier.TimeDataL2Partition

/-! Plancherel and exact scaling of the actual band-symbol weighted data.
The multiplier is retained throughout; no unweighted partial transform
is substituted for it. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

/-- The actual forward Fourier transform, transported back to the original
product-norm plane as a Schwartz function. -/
def planeFourierSchwartz (f : SchwartzMap Plane ℂ) : SchwartzMap Plane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv.symm
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv f))

@[simp] theorem planeFourierSchwartz_apply (f : SchwartzMap Plane ℂ) (ξ : Plane) :
    planeFourierSchwartz f ξ = planeFourierIntegral f ξ := by
  rw [planeFourierIntegral_eq_euclidean]
  exact congrFun (SchwartzMap.fourier_coe _) (fourierPlaneEquiv.symm ξ)

theorem planeFourierIntegral_contDiff (f : SchwartzMap Plane ℂ) :
    ContDiff ℝ ∞ (planeFourierIntegral f) := by
  simpa only [show ⇑(planeFourierSchwartz f) = planeFourierIntegral f from
    funext (planeFourierSchwartz_apply f)] using (planeFourierSchwartz f).smooth ⊤

/-- Squared Plancherel mass in the original product Lebesgue measure. -/
theorem lintegral_planeFourierIntegral_sq (f : SchwartzMap Plane ℂ) :
    (∫⁻ ξ : Plane, ‖planeFourierIntegral f ξ‖ₑ ^ (2 : ℕ)) =
      ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  let fE := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv f
  calc
    _ = ∫⁻ ξ : FourierPlane,
        ‖planeFourierIntegral f (WithLp.ofLp ξ)‖ₑ ^ (2 : ℕ) :=
      ((WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp
        ((planeFourierIntegral_contDiff f).continuous.enorm.measurable.pow_const _)).symm
    _ = ∫⁻ ξ : FourierPlane, ‖𝓕 (⇑fE) ξ‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro ξ
      rw [planeFourierIntegral_eq_euclidean]
      rfl
    _ = ∫⁻ x : FourierPlane, ‖fE x‖ₑ ^ (2 : ℕ) := lintegral_enorm_sq_fourier fE
    _ = ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) :=
      (WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp
        (f.continuous.enorm.measurable.pow_const _)

theorem weighted_scaledFourierData_contDiff {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (f : SchwartzMap Plane ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
  (Complex.ofRealCLM.contDiff.comp hm).mul
    ((planeFourierIntegral_contDiff f).comp
      (show ContDiff ℝ ∞ (fun ξ : Plane => r • ξ) by fun_prop))

/-- Exact partial Plancherel for the real compact symbol multiplying the
actual scaled Fourier transform. -/
theorem lintegral_weightedPartialFourierData_sq {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (f : SchwartzMap Plane ℂ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal r⁻¹ *
        ∫⁻ ξ : Plane, ‖(m ξ : ℂ) * planeFourierIntegral f (r • ξ)‖ₑ ^ (2 : ℕ) :=
  lintegral_partialFourierData_plane_sq _ (weighted_scaledFourierData_contDiff hm f r)
    ((hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right) hr

/-- The exact `r⁻¹ᐟ²` partial-transform factor in L² norm form. -/
theorem eLpNorm_weightedPartialFourierData_two {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (f : SchwartzMap Plane ℂ) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x : Plane => weightedPartialFourierData m f r x.1 x.2) 2 volume =
      ENNReal.ofReal r⁻¹ ^ (1 / (2 : ℝ)) *
        eLpNorm (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) 2 volume :=
  eLpNorm_partialFourierData_two _ (weighted_scaledFourierData_contDiff hm f r)
    ((hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right) hr

/-- Exact two-dimensional frequency dilation in the squared Fourier mass. -/
theorem lintegral_scaled_planeFourierIntegral_sq (f : SchwartzMap Plane ℂ)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ ξ : Plane, ‖planeFourierIntegral f (r • ξ)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  calc
    _ = ∫⁻ ξ : Plane, ‖planeFourierIntegral f ξ‖ₑ ^ (2 : ℕ)
        ∂Measure.map (fun ξ : Plane => r • ξ) volume :=
      (lintegral_map ((planeFourierIntegral_contDiff f).continuous.enorm.measurable.pow_const _)
        (by fun_prop)).symm
    _ = ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ ξ : Plane, ‖planeFourierIntegral f ξ‖ₑ ^ (2 : ℕ) := by
      rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure, smul_eq_mul]
      congr 1
      have hd : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
      rw [hd, abs_of_pos (inv_pos.mpr (pow_pos hr 2)), inv_pow]
    _ = _ := by rw [lintegral_planeFourierIntegral_sq]

/-- The compact multiplier contributes its actual uniform size, while the
partial Fourier transform and two-dimensional input dilation contribute
exactly `r⁻³` to the squared input mass. -/
theorem lintegral_weightedPartialFourierData_sq_le {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (f : SchwartzMap Plane ℂ) {r M : ℝ} (hr : 0 < r)
    (hbound : ∀ ξ : Plane, |m ξ| ≤ M) :
    (∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
        ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  rw [lintegral_weightedPartialFourierData_sq hm hc f hr]
  have hnorm (ξ : Plane) :
      ‖(m ξ : ℂ) * planeFourierIntegral f (r • ξ)‖ₑ ^ (2 : ℕ) ≤
        ENNReal.ofReal (M ^ (2 : ℕ)) * ‖planeFourierIntegral f (r • ξ)‖ₑ ^ (2 : ℕ) := by
    rw [enorm_mul, mul_pow, ← ofReal_norm ((m ξ : ℝ) : ℂ), Complex.norm_real,
      Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (abs_nonneg _) (hbound ξ) 2)) _
  calc
    _ ≤ ENNReal.ofReal r⁻¹ * ∫⁻ ξ : Plane,
        ENNReal.ofReal (M ^ (2 : ℕ)) * ‖planeFourierIntegral f (r • ξ)‖ₑ ^ (2 : ℕ) :=
      mul_le_mul_right (lintegral_mono hnorm) _
    _ = ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (M ^ (2 : ℕ)) *
        (ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_scaled_planeFourierIntegral_sq f hr]
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hr.le) (sq_nonneg M))]
      congr 2
      ring

/-- The norm version keeps all three inverse frequency Jacobians under
the square root, hence gives the exact `r⁻³ᐟ²` input scaling. -/
theorem eLpNorm_weightedPartialFourierData_two_le {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (f : SchwartzMap Plane ℂ) {r M : ℝ} (hr : 0 < r)
    (hbound : ∀ ξ : Plane, |m ξ| ≤ M) :
    eLpNorm (fun x : Plane => weightedPartialFourierData m f r x.1 x.2) 2 volume ≤
      ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) ^ (1 / (2 : ℝ)) *
        eLpNorm f 2 volume := by
  have he (g : Plane → ℂ) : eLpNorm g 2 volume =
      (∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (f := g) (μ := volume)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)))
  rw [he, he]
  calc
    _ ≤ (ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
        ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow (lintegral_weightedPartialFourierData_sq_le hm hc f hr hbound)
        (by norm_num : 0 ≤ 1 / (2 : ℝ))
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ 1 / (2 : ℝ))

/-- Actual compact-symbol data localized into all time pieces, with both
frequency Jacobians and the uniform squared-sum constant one. -/
theorem sum_lintegral_timeLocalized_weightedPartialFourierData_sq_le
    (b δ : ℝ) (N : ℕ) {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (f : SchwartzMap Plane ℂ) {r M : ℝ} (hr : 0 < r)
    (hbound : ∀ ξ : Plane, |m ξ| ≤ M) :
    (∑ i ∈ Finset.range N, ∫⁻ x : Plane,
      ‖timeLocalizedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2) x‖ₑ ^
        (2 : ℕ)) ≤
      ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
        ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  calc
    _ ≤ ∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ) :=
      sum_lintegral_timeLocalizedData_sq_le b δ N
        (stronglyMeasurable_partialFourierData
          (weighted_scaledFourierData_contDiff hm f r).continuous r)
    _ ≤ _ := lintegral_weightedPartialFourierData_sq_le hm hc f hr hbound

/-- A fixed smooth compact symbol determines a genuine frequency- and
input-independent squared L² constant for the partial Fourier data. -/
theorem exists_uniform_weightedPartialFourierData_L2_mass_bound
    {m : Plane → ℝ} (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : SchwartzMap Plane ℂ) (r : ℝ), 0 < r →
      (∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ)) ≤
        ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨ξ₀, hξ₀⟩ := hm.continuous.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨‖m ξ₀‖, norm_nonneg _, ?_⟩
  intro f r hr
  exact lintegral_weightedPartialFourierData_sq_le hm hc f hr
    (fun ξ => by simpa only [Real.norm_eq_abs] using hξ₀ ξ)

/-- The same symbol constant works for every time partition, including
all centers, widths, and numbers of pieces. -/
theorem exists_uniform_timeLocalized_weightedPartialFourierData_L2_mass_bound
    {m : Plane → ℝ} (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : SchwartzMap Plane ℂ) (r b δ : ℝ) (N : ℕ), 0 < r →
      (∑ i ∈ Finset.range N, ∫⁻ x : Plane,
        ‖timeLocalizedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2) x‖ₑ ^
          (2 : ℕ)) ≤
        ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨ξ₀, hξ₀⟩ := hm.continuous.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨‖m ξ₀‖, norm_nonneg _, ?_⟩
  intro f r b δ N hr
  exact sum_lintegral_timeLocalized_weightedPartialFourierData_sq_le b δ N hm hc f hr
    (fun ξ => by simpa only [Real.norm_eq_abs] using hξ₀ ξ)

end PlanarNikodym
