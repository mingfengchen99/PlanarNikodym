import PlanarNikodym.Analysis.Fourier.ComplexSymbolKernels
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Physical kernels and pointwise Holder estimates for the actual scaled
complex-symbol Fourier operator. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace PlanarNikodym

theorem planeFourierCharacter_smul_swap (r : ℝ) (x ξ : Plane) :
    planeFourierCharacter x (r • ξ) = planeFourierCharacter (r • x) ξ := by
  unfold planeFourierCharacter fourierPhase
  congr 3
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The scaled Fourier operator uses the original input Fourier integral
and the true two-dimensional Jacobian. -/
def scaledSymbolOperator (S : SchwartzMap Plane ℂ) (r : ℝ) (f : Plane → ℂ) : ℂ :=
  r ^ 2 • ∫ ξ : Plane, S ξ * planeFourierIntegral f (r • ξ)

theorem integrable_complex_symbol_spatial_frequency (S : SchwartzMap Plane ℂ)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    Integrable (fun p : Plane × Plane =>
      S p.1 * planeFourierCharacter (-p.2) (r • p.1) * f p.2)
      (volume.prod volume) := by
  apply (S.integrable.norm.mul_prod hf.norm).mono'
  · exact ((S.continuous.comp continuous_fst).mul
      (continuous_planeFourierCharacter.comp
        (continuous_snd.neg.prodMk (continuous_const.smul continuous_fst)))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd
  · filter_upwards [] with x
    simp

/-- Absolute Fubini identifies the actual scaled frequency integral with
its actual inverse-symbol kernel, for all L1 inputs. -/
theorem scaledSymbolOperator_eq_kernel (S : SchwartzMap Plane ℂ)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    scaledSymbolOperator S r f =
      r ^ 2 • ∫ y : Plane, planeInverseFourierSchwartzCLM S (r • (-y)) * f y := by
  unfold scaledSymbolOperator
  congr 1
  calc
    _ = ∫ ξ : Plane, ∫ y : Plane,
        S ξ * planeFourierCharacter (-y) (r • ξ) * f y := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [planeFourierIntegral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ∫ y : Plane, ∫ ξ : Plane,
        S ξ * planeFourierCharacter (-y) (r • ξ) * f y :=
      integral_integral_swap (integrable_complex_symbol_spatial_frequency S hf r)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [planeInverseFourierSchwartzCLM_apply, ← integral_mul_const]
      simp only [planeFourierCharacter_smul_swap]

/-- Expansion of the frequency scale cannot increase an Lp kernel norm.
This includes p = 1 and p = ∞. -/
theorem eLpNorm_plane_dilate_le (K : Plane → ℂ) (hK : Continuous K)
    {r : ℝ} (hr : 1 ≤ r) (p : ℝ≥0∞) :
    eLpNorm (fun y : Plane => K (r • y)) p volume ≤ eLpNorm K p volume := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  change eLpNorm (K ∘ fun y : Plane => r • y) p volume ≤ _
  rw [← eLpNorm_map_measure (p := p) (g := K) (μ := (volume : Measure Plane))
    hK.aestronglyMeasurable (measurable_const_smul r).aemeasurable]
  apply eLpNorm_mono_measure
  rw [Measure.map_addHaar_smul volume hrpos.ne']
  have hpow : (1 : ℝ) ≤ r ^ Module.finrank ℝ Plane := one_le_pow₀ hr
  have hc : ENNReal.ofReal (abs (r ^ Module.finrank ℝ Plane)⁻¹) ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hpow)), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ hpow)
  intro s
  simpa only [Measure.smul_apply, smul_eq_mul, one_mul] using
    (mul_le_mul_left hc (volume s))

set_option maxHeartbeats 600000 in
/-- Pointwise Holder bound for the actual scaled Fourier operator. The
symbol kernel is on the original plane, with no additional measurability
assumption on an abstract operator or representative. -/
theorem scaledSymbolOperator_enorm_le (S : SchwartzMap Plane ℂ)
    {f : Plane → ℂ} (hf : Integrable f) {r : ℝ} (hr : 1 ≤ r)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate q p] :
    ‖scaledSymbolOperator S r f‖ₑ ≤ ENNReal.ofReal (r ^ 2) *
      eLpNorm (planeInverseFourierSchwartzCLM S) q volume * eLpNorm f p volume := by
  let K := planeInverseFourierSchwartzCLM S
  rw [scaledSymbolOperator_eq_kernel S hf r, enorm_smul]
  have hr2 : ‖r ^ 2‖ₑ = ENNReal.ofReal (r ^ 2) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg r)]
  rw [hr2]
  apply (mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _).trans
  have hHolder : (∫⁻ y : Plane, ‖K (r • (-y)) * f y‖ₑ) ≤
      eLpNorm (fun y : Plane => K (r • (-y))) q volume * eLpNorm f p volume := by
    change (∫⁻ y : Plane, ‖((fun y : Plane => K (r • (-y))) • f) y‖ₑ) ≤ _
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℂ) hf.aestronglyMeasurable
      ((K.continuous.comp (continuous_const.smul continuous_neg)).aestronglyMeasurable)
  have hnorm : eLpNorm (fun y : Plane => K (r • (-y))) q volume ≤ eLpNorm K q volume := by
    have he := eLpNorm_comp_measurePreserving (p := q)
      (g := fun y : Plane => K (r • y))
      (K.continuous.comp (continuous_const.smul continuous_id)).aestronglyMeasurable
      (Measure.measurePreserving_neg (volume : Measure Plane))
    change eLpNorm ((fun y : Plane => K (r • y)) ∘ Neg.neg) q volume = _ at he
    rw [show (fun y : Plane => K (r • (-y))) =
      (fun y : Plane => K (r • y)) ∘ Neg.neg from rfl, he]
    exact eLpNorm_plane_dilate_le K K.continuous hr q
  calc
    _ ≤ ENNReal.ofReal (r ^ 2) *
        (eLpNorm (fun y : Plane => K (r • (-y))) q volume * eLpNorm f p volume) :=
      mul_le_mul_right hHolder _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_right (mul_le_mul_left hnorm (eLpNorm f p volume))
        (ENNReal.ofReal (r ^ 2))

end PlanarNikodym
