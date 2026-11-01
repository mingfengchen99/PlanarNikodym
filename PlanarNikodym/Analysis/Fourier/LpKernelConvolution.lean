import PlanarNikodym.Analysis.Fourier.SchwartzJetConvolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Young's inequality for the actual convolution used by the frequency bands.
The proof uses Hölder in the kernel measure and Tonelli in physical space. -/
noncomputable section
open Set MeasureTheory
open scoped Convolution NNReal ENNReal

namespace PlanarNikodym

/-- The power form of the finite-exponent averaging estimate. This also
includes `p = 1` and the zero measure, without a normalization by the mass. -/
theorem lintegral_norm_average_rpow_le (ν : Measure Plane) [SFinite ν]
    {f : Plane → ℂ} (hf : StronglyMeasurable f) {p : ℝ≥0} (hp : 1 ≤ p) :
    (∫⁻ x : Plane, (∫⁻ y : Plane, ‖f (x - y)‖ₑ ∂ν) ^ (p : ℝ)) ≤
      (∫⁻ x : Plane, ‖f x‖ₑ ^ (p : ℝ)) * (ν univ) ^ (p : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hpow (x : Plane) :
      (∫⁻ y : Plane, ‖f (x - y)‖ₑ ∂ν) ^ (p : ℝ) ≤
        (∫⁻ y : Plane, ‖f (x - y)‖ₑ ^ (p : ℝ) ∂ν) *
          (ν univ) ^ ((p : ℝ) - 1) := by
    have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
      (μ := ν) (f := fun y : Plane => f (x - y)) zero_lt_one hp1
      (hf.comp_measurable (measurable_id.const_sub x)).aestronglyMeasurable
    simp only [eLpNorm'_eq_lintegral_enorm, div_one, ENNReal.rpow_one] at h
    have h := ENNReal.rpow_le_rpow h hp0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul] at h
    have he1 : (1 / (p : ℝ)) * p = 1 := div_mul_cancel₀ 1 hp0.ne'
    have he2 : (1 - 1 / (p : ℝ)) * p = (p : ℝ) - 1 := by field_simp
    simpa only [he1, he2, ENNReal.rpow_one] using h
  have hmeas : Measurable (fun z : Plane × Plane => ‖f (z.1 - z.2)‖ₑ ^ (p : ℝ)) :=
    (hf.measurable.comp (measurable_fst.sub measurable_snd)).enorm.pow_const _
  calc
    _ ≤ ∫⁻ x : Plane, (∫⁻ y : Plane, ‖f (x - y)‖ₑ ^ (p : ℝ) ∂ν) *
        (ν univ) ^ ((p : ℝ) - 1) := lintegral_mono hpow
    _ = (∫⁻ x : Plane, ∫⁻ y : Plane, ‖f (x - y)‖ₑ ^ (p : ℝ) ∂ν) *
        (ν univ) ^ ((p : ℝ) - 1) :=
      lintegral_mul_const _ hmeas.lintegral_prod_right
    _ = (∫⁻ y : Plane, (∫⁻ x : Plane, ‖f (x - y)‖ₑ ^ (p : ℝ)) ∂ν) *
        (ν univ) ^ ((p : ℝ) - 1) := by
      rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ = ((∫⁻ x : Plane, ‖f x‖ₑ ^ (p : ℝ)) * ν univ) *
        (ν univ) ^ ((p : ℝ) - 1) := by
      congr 1
      have htrans (y : Plane) :
          (∫⁻ x : Plane, ‖f (x - y)‖ₑ ^ (p : ℝ)) = ∫⁻ x : Plane, ‖f x‖ₑ ^ (p : ℝ) :=
        (measurePreserving_sub_right (volume : Measure Plane) y).lintegral_comp
          (hf.measurable.enorm.pow_const _)
      simp_rw [htrans]
      exact lintegral_const _
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        ν univ * (ν univ) ^ ((p : ℝ) - 1) =
            (ν univ) ^ (1 : ℝ) * (ν univ) ^ ((p : ℝ) - 1) := by rw [ENNReal.rpow_one]
        _ = (ν univ) ^ (1 + ((p : ℝ) - 1)) :=
          (ENNReal.rpow_add_of_nonneg _ _ zero_le_one (sub_nonneg.mpr hp1)).symm
        _ = _ := by congr 1; ring

/-- Finite-exponent Young inequality for a Schwartz kernel and a strongly
measurable scalar input. The right side is allowed to be infinite. -/
theorem eLpNorm_convolution_schwartz_smul_le_of_stronglyMeasurable
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]
    {f : Plane → ℂ} (hf : StronglyMeasurable f) (K : SchwartzMap Plane F)
    {p : ℝ≥0} (hp : 1 ≤ p) :
    eLpNorm (f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] K) p volume ≤
      eLpNorm f p volume * eLpNorm K 1 volume := by
  let ν : Measure Plane := volume.withDensity (fun y => ‖K y‖ₑ)
  have hmass : ν univ = ∫⁻ y : Plane, ‖K y‖ₑ := by
    simp [ν, withDensity_apply _ MeasurableSet.univ]
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    (K.integrable (μ := volume)).hasFiniteIntegral.ne
  have hbound (x : Plane) :
      ‖(f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] K) x‖ₑ ≤
        ∫⁻ y : Plane, ‖f (x - y)‖ₑ ∂ν := by
    rw [convolution_eq_swap (ContinuousLinearMap.lsmul ℝ ℂ)]
    simp only [ContinuousLinearMap.lsmul_apply]
    apply (enorm_integral_le_lintegral_enorm _).trans_eq
    dsimp only [ν]
    have hg : Measurable (fun y : Plane => ‖f (x - y)‖ₑ) :=
      (hf.measurable.comp (measurable_id.const_sub x)).enorm
    rw [lintegral_withDensity_eq_lintegral_mul volume K.continuous.enorm.measurable hg]
    apply lintegral_congr
    intro y
    simp only [Pi.mul_apply, enorm_smul, mul_comm]
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp)
  apply (ENNReal.rpow_le_rpow_iff hpR).mp
  rw [eLpNorm_nnreal_pow_eq_lintegral hp0,
    ENNReal.mul_rpow_of_nonneg _ _ hpR.le, eLpNorm_nnreal_pow_eq_lintegral hp0,
    eLpNorm_one_eq_lintegral_enorm]
  calc
    _ ≤ ∫⁻ x : Plane, (∫⁻ y : Plane, ‖f (x - y)‖ₑ ∂ν) ^ (p : ℝ) :=
      lintegral_mono (fun x => ENNReal.rpow_le_rpow (hbound x) hpR.le)
    _ ≤ _ := by simpa only [hmass] using lintegral_norm_average_rpow_le ν hf hp

/-- Young inequality for the actual convolution, for every finite `p ≥ 1`.
Only L1 regularity of the input is used to select its measurable representative;
no smoothness or compact support of the input is required. -/
theorem eLpNorm_convolution_schwartz_smul_le
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]
    {f : Plane → ℂ} (hf : Integrable f) (K : SchwartzMap Plane F)
    {p : ℝ≥0} (hp : 1 ≤ p) :
    eLpNorm (f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] K) p volume ≤
      eLpNorm f p volume * eLpNorm K 1 volume := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℂ) hfg Filter.EventuallyEq.rfl,
    eLpNorm_congr_ae hfg]
  exact eLpNorm_convolution_schwartz_smul_le_of_stronglyMeasurable
    hf.aestronglyMeasurable.stronglyMeasurable_mk K hp

end PlanarNikodym
