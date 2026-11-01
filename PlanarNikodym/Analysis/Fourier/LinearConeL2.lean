import PlanarNikodym.Analysis.Fourier.LinearConeRepresentation
import PlanarNikodym.Analysis.Fourier.ConeFrequencyL2

/-! A genuine degree-one cone L² operator estimate. The proof uses the
actual nonlinear frequency substitution followed by planar Plancherel;
the resulting `r⁻¹` norm decay is uniform over all input data and time
supports. The variable-amplitude operator is treated separately. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

/-- Plancherel for the actual inverse Fourier transform on the original
product-norm plane. -/
theorem lintegral_planeInverseFourierSchwartz_sq (f : SchwartzMap Plane ℂ) :
    (∫⁻ x : Plane, ‖planeInverseFourierSchwartzCLM f x‖ₑ ^ (2 : ℕ)) =
      ∫⁻ ξ : Plane, ‖f ξ‖ₑ ^ (2 : ℕ) := by
  let fE := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv f
  calc
    _ = ∫⁻ x : FourierPlane,
        ‖planeInverseFourierSchwartzCLM f (WithLp.ofLp x)‖ₑ ^ (2 : ℕ) :=
      ((WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp
        ((planeInverseFourierSchwartzCLM f).continuous.enorm.measurable.pow_const _)).symm
    _ = ∫⁻ x : FourierPlane, ‖𝓕⁻ (⇑fE) x‖ₑ ^ (2 : ℕ) := by
      simp only [← SchwartzMap.fourierInv_coe]
      rfl
    _ = ∫⁻ ξ : FourierPlane, ‖fE ξ‖ₑ ^ (2 : ℕ) := lintegral_enorm_sq_fourierInv fE
    _ = ∫⁻ ξ : Plane, ‖f ξ‖ₑ ^ (2 : ℕ) :=
      (WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp
        (f.continuous.enorm.measurable.pow_const _)

/-- Exact planar inverse Fourier dilation. -/
theorem lintegral_scaled_planeInverseFourierSchwartz_sq (f : SchwartzMap Plane ℂ)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Plane, ‖planeInverseFourierSchwartzCLM f (r • x)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) * ∫⁻ ξ : Plane, ‖f ξ‖ₑ ^ (2 : ℕ) := by
  calc
    _ = ∫⁻ x : Plane, ‖planeInverseFourierSchwartzCLM f x‖ₑ ^ (2 : ℕ)
        ∂Measure.map (fun x : Plane => r • x) volume :=
      (lintegral_map ((planeInverseFourierSchwartzCLM f).continuous.enorm.measurable.pow_const _)
        (by fun_prop)).symm
    _ = ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ‖planeInverseFourierSchwartzCLM f x‖ₑ ^ (2 : ℕ) := by
      rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure, smul_eq_mul]
      congr 1
      have hd : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
      rw [hd, abs_of_pos (inv_pos.mpr (pow_pos hr 2)), inv_pow]
    _ = _ := by rw [lintegral_planeInverseFourierSchwartz_sq]

theorem continuous_linearConeExtension (h : Plane → ℂ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) (r : ℝ) :
    Continuous (linearConeExtension h r) := by
  have he : linearConeExtension h r = fun w : Plane =>
      planeInverseFourierSchwartzCLM (coneFrequencySchwartz h hh hc ha hgap) (r • w) :=
    funext (linearConeExtension_eq_inverseFourierSchwartz h hh hc ha hgap r)
  rw [he]
  exact (planeInverseFourierSchwartzCLM _).continuous.comp (continuous_const.smul continuous_id)

/-- Exact squared L² identity for the true cone extension integral. -/
theorem lintegral_linearConeExtension_sq (h : Plane → ℂ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ w : Plane, ‖linearConeExtension h r w‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ENNReal.ofReal |x.2|⁻¹ * ‖h x‖ₑ ^ (2 : ℕ) := by
  simp_rw [linearConeExtension_eq_inverseFourierSchwartz h hh hc ha hgap r]
  rw [lintegral_scaled_planeInverseFourierSchwartz_sq _ hr]
  change ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
      (∫⁻ ξ : Plane, ‖coneFrequencyData h ξ‖ₑ ^ (2 : ℕ)) = _
  rw [lintegral_coneFrequencyData_sq hh.continuous.measurable]

/-- The genuine `r⁻²` squared-operator bound from the inverse Jacobian
and a real vertical-frequency gap. -/
theorem lintegral_linearConeExtension_sq_le (h : Plane → ℂ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ w : Plane, ‖linearConeExtension h r w‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  simp_rw [linearConeExtension_eq_inverseFourierSchwartz h hh hc ha hgap r]
  rw [lintegral_scaled_planeInverseFourierSchwartz_sq _ hr]
  change ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
      (∫⁻ ξ : Plane, ‖coneFrequencyData h ξ‖ₑ ^ (2 : ℕ)) ≤ _
  calc
    _ ≤ ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        (ENNReal.ofReal a⁻¹ * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) :=
      mul_le_mul_right (lintegral_coneFrequencyData_sq_le hh.continuous.measurable ha hgap) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm (r⁻¹ ^ (2 : ℕ))]

/-- The actual no-amplitude model has the required `r⁻¹` L² decay;
its constant depends only on the vertical-frequency gap. -/
theorem eLpNorm_linearConeExtension_two_le (h : Plane → ℂ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    eLpNorm (linearConeExtension h r) 2 volume ≤
      ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) * eLpNorm h 2 volume := by
  have he (g : Plane → ℂ) : eLpNorm g 2 volume =
      (∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (f := g) (μ := volume)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)))
  rw [he, he]
  calc
    _ ≤ (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow (lintegral_linearConeExtension_sq_le h hh hc ha hr hgap)
        (by norm_num : 0 ≤ 1 / (2 : ℝ))
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ 1 / (2 : ℝ))

end PlanarNikodym
