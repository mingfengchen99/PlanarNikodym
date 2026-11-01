import PlanarNikodym.Analysis.Fourier.ConeFrequencyCoordinates

/-! Exact squared L² change of variables for the cone input coordinates.
One inverse vertical-frequency weight remains after the actual nonlinear
Jacobian; a frequency gap bounds it uniformly. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem measurable_coneFrequencyData {h : Plane → ℂ} (hh : Measurable h) :
    Measurable (coneFrequencyData h) := by
  unfold coneFrequencyData coneFrequencyInverse
  exact (by fun_prop : Measurable (fun ξ : Plane => |ξ.1|⁻¹)).smul
    (hh.comp (by fun_prop))

/-- The inner change of variables carries exactly one factor `|η|`. -/
theorem lintegral_coneFrequencyData_slice_sq {h : Plane → ℂ}
    (hh : Measurable h) (η : ℝ) :
    (∫⁻ ν : ℝ, ‖coneFrequencyData h (η, ν)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal |η|⁻¹ * ∫⁻ τ : ℝ, ‖h (τ, η)‖ₑ ^ (2 : ℕ) := by
  by_cases hη : η = 0
  · subst η
    simp [coneFrequencyData]
  · have hF : Measurable (fun τ : ℝ => ‖h (τ, η)‖ₑ ^ (2 : ℕ)) :=
      ((hh.comp (measurable_id.prodMk measurable_const)).enorm).pow_const _
    have hEq : (∫⁻ ν : ℝ, ‖h (ν / η, η)‖ₑ ^ (2 : ℕ)) =
        ENNReal.ofReal |η| * ∫⁻ τ : ℝ, ‖h (τ, η)‖ₑ ^ (2 : ℕ) := by
      have he : (fun ν : ℝ => ‖h (ν / η, η)‖ₑ ^ (2 : ℕ)) =
          (fun τ : ℝ => ‖h (τ, η)‖ₑ ^ (2 : ℕ)) ∘ (fun ν : ℝ => η⁻¹ * ν) := by
        funext ν
        simp only [Function.comp_def, div_eq_mul_inv, mul_comm]
      rw [he]
      dsimp only [Function.comp_def]
      rw [← lintegral_map hF (show Measurable (fun ν : ℝ => η⁻¹ * ν) by fun_prop),
        Real.map_volume_mul_left (inv_ne_zero hη),
        inv_inv, lintegral_smul_measure, smul_eq_mul]
    have hnorm (ν : ℝ) : ‖coneFrequencyData h (η, ν)‖ₑ ^ (2 : ℕ) =
        ENNReal.ofReal (|η|⁻¹ ^ (2 : ℕ)) * ‖h (ν / η, η)‖ₑ ^ (2 : ℕ) := by
      rw [coneFrequencyData, enorm_smul, mul_pow,
        Real.enorm_eq_ofReal (inv_nonneg.mpr (abs_nonneg η)),
        ← ENNReal.ofReal_pow (inv_nonneg.mpr (abs_nonneg η))]
      rfl
    simp_rw [hnorm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hEq, ← mul_assoc,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 2
    field_simp [abs_ne_zero.mpr hη]

/-- The exact full cone-frequency Jacobian in L². -/
theorem lintegral_coneFrequencyData_sq {h : Plane → ℂ} (hh : Measurable h) :
    (∫⁻ ξ : Plane, ‖coneFrequencyData h ξ‖ₑ ^ (2 : ℕ)) =
      ∫⁻ x : Plane, ENNReal.ofReal |x.2|⁻¹ * ‖h x‖ₑ ^ (2 : ℕ) := by
  rw [Measure.volume_eq_prod,
    lintegral_prod _ ((measurable_coneFrequencyData hh).enorm.pow_const _).aemeasurable,
    lintegral_prod_symm _ (by fun_prop)]
  apply lintegral_congr
  intro η
  dsimp only [Prod.snd]
  rw [lintegral_coneFrequencyData_slice_sq hh,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- A genuine frequency gap gives a uniform input L² bound for the cone
coordinates, with the actual inverse Jacobian and no hidden scale loss. -/
theorem lintegral_coneFrequencyData_sq_le {h : Plane → ℂ} (hh : Measurable h)
    {a : ℝ} (ha : 0 < a) (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ ξ : Plane, ‖coneFrequencyData h ξ‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal a⁻¹ * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  rw [lintegral_coneFrequencyData_sq hh,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  by_cases hxa : |x.2| < a
  · simp [hgap x hxa]
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (inv_anti₀ ha (le_of_not_gt hxa))) _

/-- The cone input substitution preserves the full L¹ mass. The missing
vertex fiber is a null set in the outer vertical-frequency variable. -/
theorem lintegral_coneFrequencyData_enorm {h : Plane → ℂ} (hh : Measurable h) :
    (∫⁻ ξ : Plane, ‖coneFrequencyData h ξ‖ₑ) = ∫⁻ x : Plane, ‖h x‖ₑ := by
  rw [Measure.volume_eq_prod,
    lintegral_prod _ (measurable_coneFrequencyData hh).enorm.aemeasurable,
    lintegral_prod_symm _ hh.enorm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with η hη
  have hF : Measurable (fun τ : ℝ => ‖h (τ, η)‖ₑ) :=
    (hh.comp (measurable_id.prodMk measurable_const)).enorm
  have hEq : (∫⁻ ν : ℝ, ‖h (ν / η, η)‖ₑ) =
      ENNReal.ofReal |η| * ∫⁻ τ : ℝ, ‖h (τ, η)‖ₑ := by
    have he : (fun ν : ℝ => ‖h (ν / η, η)‖ₑ) =
        (fun τ : ℝ => ‖h (τ, η)‖ₑ) ∘ (fun ν : ℝ => η⁻¹ * ν) := by
      funext ν
      simp only [Function.comp_def, div_eq_mul_inv, mul_comm]
    rw [he]
    dsimp only [Function.comp_def]
    rw [← lintegral_map hF (show Measurable (fun ν : ℝ => η⁻¹ * ν) by fun_prop),
      Real.map_volume_mul_left (inv_ne_zero hη), inv_inv, lintegral_smul_measure, smul_eq_mul]
  have hnorm (ν : ℝ) : ‖coneFrequencyData h (η, ν)‖ₑ =
      ENNReal.ofReal |η|⁻¹ * ‖h (ν / η, η)‖ₑ := by
    rw [coneFrequencyData, enorm_smul,
      Real.enorm_eq_ofReal (inv_nonneg.mpr (abs_nonneg η))]
    rfl
  simp_rw [hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hEq, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg η)),
    inv_mul_cancel₀ (abs_ne_zero.mpr hη), ENNReal.ofReal_one, one_mul]

theorem integrable_coneFrequencyData {h : Plane → ℂ}
    (hh : Measurable h) (hi : Integrable h) : Integrable (coneFrequencyData h) := by
  refine ⟨(measurable_coneFrequencyData hh).aestronglyMeasurable, ?_⟩
  change (∫⁻ ξ : Plane, ‖coneFrequencyData h ξ‖ₑ) < (∞ : ℝ≥0∞)
  rw [lintegral_coneFrequencyData_enorm hh]
  exact hi.hasFiniteIntegral

/-- General measurable L² inputs remain in L² under the actual cone
frequency substitution whenever the vertical frequency has a gap. -/
theorem memLp_coneFrequencyData_two {h : Plane → ℂ} (hh : Measurable h)
    (h2 : MemLp h 2 volume) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    MemLp (coneFrequencyData h) 2 volume := by
  have hmass : (∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) < (∞ : ℝ≥0∞) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) h2.2)
  refine ⟨(measurable_coneFrequencyData hh).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact (lintegral_coneFrequencyData_sq_le hh ha hgap).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass)

end PlanarNikodym
