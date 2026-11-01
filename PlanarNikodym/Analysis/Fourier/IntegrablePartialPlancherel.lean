import PlanarNikodym.Analysis.Fourier.PlaneIntegralPlancherel
import PlanarNikodym.Analysis.Fourier.WeightedPartialPlancherel

/-! Partial Plancherel for continuous compact frequency data, and the
actual weighted partial data of a general L¹∩L² original input. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal
namespace PlanarNikodym

theorem hasCompactSupport_partialFrequencySlice {a : Plane → ℂ}
    (hc : HasCompactSupport a) (η : ℝ) : HasCompactSupport (fun ξ : ℝ => a (ξ, η)) := by
  apply HasCompactSupport.intro (hc.isCompact.image continuous_fst)
  intro ξ hξ
  exact image_eq_zero_of_notMem_tsupport (fun hmem => hξ ⟨(ξ, η), hmem, rfl⟩)

theorem lintegral_partialFourierData_sq_of_continuous {a : Plane → ℂ}
    (ha : Continuous a) (hc : HasCompactSupport a) {r : ℝ} (hr : 0 < r) (η : ℝ) :
    (∫⁻ t : ℝ, ‖partialFourierData a r t η‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal r⁻¹ * ∫⁻ ξ : ℝ, ‖a (ξ, η)‖ₑ ^ (2 : ℕ) := by
  let f : ℝ → ℂ := fun ξ => a (ξ, η)
  have hf : Continuous f := ha.comp (continuous_id.prodMk continuous_const)
  have hfc : HasCompactSupport f := hasCompactSupport_partialFrequencySlice hc η
  have h1 : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have h2 : MemLp f 2 := hf.memLp_of_hasCompactSupport hfc
  have hcont : Continuous (𝓕⁻ f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg h1
  calc
    _ = ∫⁻ t : ℝ, ‖𝓕⁻ f (r * t)‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro t
      rw [partialFourierData_eq_fourierInv]
    _ = ∫⁻ t : ℝ, ‖𝓕⁻ f t‖ₑ ^ (2 : ℕ)
        ∂Measure.map (fun t : ℝ => r * t) volume :=
      (lintegral_map (hcont.enorm.measurable.pow_const _) (by fun_prop)).symm
    _ = ENNReal.ofReal r⁻¹ * ∫⁻ t : ℝ, ‖𝓕⁻ f t‖ₑ ^ (2 : ℕ) := by
      rw [Real.map_volume_mul_left hr.ne', abs_of_pos (inv_pos.mpr hr),
        lintegral_smul_measure, smul_eq_mul]
    _ = _ := by rw [lintegral_fourierInvIntegral_sq h1 h2]

theorem lintegral_partialFourierData_plane_sq_of_continuous {a : Plane → ℂ}
    (ha : Continuous a) (hc : HasCompactSupport a) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Plane, ‖partialFourierData a r x.1 x.2‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal r⁻¹ * ∫⁻ ξ : Plane, ‖a ξ‖ₑ ^ (2 : ℕ) := by
  rw [Measure.volume_eq_prod,
    lintegral_prod_symm _ ((stronglyMeasurable_partialFourierData ha r).enorm.pow_const _).aemeasurable]
  simp_rw [lintegral_partialFourierData_sq_of_continuous ha hc hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_prod_symm _ (ha.enorm.measurable.pow_const _).aemeasurable]

theorem lintegral_scaled_planeFourierIntegral_sq_of_integrable {f : Plane → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) {r : ℝ} (hr : 0 < r) :
    (∫⁻ ξ : Plane, ‖planeFourierIntegral f (r • ξ)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  calc
    _ = ∫⁻ ξ : Plane, ‖planeFourierIntegral f ξ‖ₑ ^ (2 : ℕ)
        ∂Measure.map (fun ξ : Plane => r • ξ) volume :=
      (lintegral_map ((continuous_planeFourierIntegral h1).enorm.measurable.pow_const _)
        (by fun_prop)).symm
    _ = ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ ξ : Plane, ‖planeFourierIntegral f ξ‖ₑ ^ (2 : ℕ) := by
      rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure, smul_eq_mul]
      congr 1
      have hd : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
      rw [hd, abs_of_pos (inv_pos.mpr (pow_pos hr 2)), inv_pow]
    _ = _ := by rw [lintegral_planeFourierIntegral_sq_of_integrable h1 h2]

/-- The partial inverse remains the actual integral for every integrable
input, with no Schwartz or differentiability assumption on that input. -/
theorem lintegral_weightedPartialFourierData_sq_of_integrable
    {m : Plane → ℝ} (hm : Continuous m) (hc : HasCompactSupport m)
    {f : Plane → ℂ} (h1 : Integrable f) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal r⁻¹ *
        ∫⁻ ξ : Plane, ‖(m ξ : ℂ) * planeFourierIntegral f (r • ξ)‖ₑ ^ (2 : ℕ) :=
  lintegral_partialFourierData_plane_sq_of_continuous
    (weighted_scaledFourierData_continuous hm h1 r)
    ((hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right) hr

/-- The genuine compact multiplier bound holds for arbitrary L¹∩L² input. -/
theorem lintegral_weightedPartialFourierData_sq_le_of_integrable {m : Plane → ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m)
    {f : Plane → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) {r M : ℝ} (hr : 0 < r)
    (hbound : ∀ ξ : Plane, |m ξ| ≤ M) :
    (∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
        ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  rw [lintegral_weightedPartialFourierData_sq_of_integrable hm hc h1 hr]
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
        lintegral_scaled_planeFourierIntegral_sq_of_integrable h1 h2 hr]
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hr.le) (sq_nonneg M))]
      congr 2
      ring


/-- All time windows share the same genuine input mass bound on L¹∩L². -/
theorem sum_lintegral_timeLocalized_weightedPartialFourierData_sq_le_of_integrable
    (b δ : ℝ) (N : ℕ) {m : Plane → ℝ} (hm : Continuous m) (hc : HasCompactSupport m)
    {f : Plane → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) {r M : ℝ}
    (hr : 0 < r) (hbound : ∀ ξ : Plane, |m ξ| ≤ M) :
    (∑ i ∈ Finset.range N, ∫⁻ x : Plane,
      ‖timeLocalizedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2) x‖ₑ ^
        (2 : ℕ)) ≤
      ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
        ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  calc
    _ ≤ ∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ) :=
      sum_lintegral_timeLocalizedData_sq_le b δ N
        (stronglyMeasurable_partialFourierData (weighted_scaledFourierData_continuous hm h1 r) r)
    _ ≤ _ := lintegral_weightedPartialFourierData_sq_le_of_integrable hm hc h1 h2 hr hbound

theorem exists_uniform_timeLocalized_weightedPartialFourierData_L2_mass_bound_of_integrable
    {m : Plane → ℝ} (hm : Continuous m) (hc : HasCompactSupport m) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : Plane → ℂ), Integrable f → MemLp f 2 →
      ∀ (r b δ : ℝ) (N : ℕ), 0 < r →
      (∑ i ∈ Finset.range N, ∫⁻ x : Plane,
        ‖timeLocalizedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2) x‖ₑ ^
          (2 : ℕ)) ≤
        ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨ξ₀, hξ₀⟩ := hm.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨‖m ξ₀‖, norm_nonneg _, ?_⟩
  intro f h1 h2 r b δ N hr
  exact sum_lintegral_timeLocalized_weightedPartialFourierData_sq_le_of_integrable
    b δ N hm hc h1 h2 hr (fun ξ => by simpa only [Real.norm_eq_abs] using hξ₀ ξ)

end PlanarNikodym
