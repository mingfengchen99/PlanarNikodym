import PlanarNikodym.Analysis.Fourier.TimeDataL2Partition

/-! Actual time rescaling on general L¹∩L² data. Both norm classes and
the precise squared L² Jacobian are preserved, allowing the unsmoothed
input to enter the last-stage cone estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem lintegral_timeDataRescaling_enorm {h : Plane → ℂ} (hh : Measurable h)
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ x : Plane, ‖h (timeDataRescaling c δ x)‖ₑ) =
      ENNReal.ofReal δ⁻¹ * ∫⁻ x : Plane, ‖h x‖ₑ := by
  have hA : Measurable (timeDataRescaling c δ) := by unfold timeDataRescaling; fun_prop
  rw [← lintegral_map hh.enorm hA, map_timeDataRescaling_volume c hδ.ne',
    abs_of_pos (inv_pos.mpr hδ), lintegral_smul_measure, smul_eq_mul]

theorem lintegral_timeDataRescaling_sq {h : Plane → ℂ} (hh : Measurable h)
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ x : Plane, ‖h (timeDataRescaling c δ x)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal δ⁻¹ * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  have hA : Measurable (timeDataRescaling c δ) := by unfold timeDataRescaling; fun_prop
  rw [← lintegral_map (hh.enorm.pow_const _) hA, map_timeDataRescaling_volume c hδ.ne',
    abs_of_pos (inv_pos.mpr hδ), lintegral_smul_measure, smul_eq_mul]

theorem integrable_timeDataRescaling {h : Plane → ℂ} (hh : Measurable h)
    (hi : Integrable h) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : Plane => h (timeDataRescaling c δ x)) := by
  refine ⟨(hh.comp (by unfold timeDataRescaling; fun_prop)).aestronglyMeasurable, ?_⟩
  change (∫⁻ x : Plane, ‖h (timeDataRescaling c δ x)‖ₑ) < ∞
  rw [lintegral_timeDataRescaling_enorm hh c hδ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hi.hasFiniteIntegral

theorem memLp_timeDataRescaling_two {h : Plane → ℂ} (hh : Measurable h)
    (h2 : MemLp h 2 volume) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    MemLp (fun x : Plane => h (timeDataRescaling c δ x)) 2 volume := by
  have hmass : (∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) < ∞ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) h2.2)
  refine ⟨(hh.comp (by unfold timeDataRescaling; fun_prop)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_timeDataRescaling_sq hh c hδ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass

/-- The time Jacobian squared and the two inverse square-root Jacobians
of the input and output cancel exactly in the original slice L² bound. -/
theorem timeSlice_L2_scale_cancel {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ (2 : ℕ)) * ENNReal.ofReal δ⁻¹ * ENNReal.ofReal δ⁻¹ = 1 := by
  rw [← ENNReal.ofReal_mul (sq_nonneg δ),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg δ) (inv_nonneg.mpr hδ.le))]
  have he : δ ^ (2 : ℕ) * δ⁻¹ * δ⁻¹ = 1 := by field_simp
  rw [he, ENNReal.ofReal_one]

end PlanarNikodym
