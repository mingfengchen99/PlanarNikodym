import PlanarNikodym.Analysis.Fourier.MomentParabolicScaling
import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.Jacobian

/-! Rescaling acts on the actual cone extension and its Lebesgue norms.
No decoupling inequality is used here. Both the time Jacobian and the
coefficient-space determinant remain explicit. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

def rescaledMomentAmplitude {n : ℕ} (b : Aux (n + 1) → ℝ → ℝ → ℂ)
    (c δ : ℝ) (hδ : δ ≠ 0) (w : Aux (n + 1)) (t η : ℝ) : ℂ :=
  b ((momentParabolicMap n c δ hδ).symm w) (c + δ * t) η * timePartitionWindow t

theorem timeSliceExtension_moment_rescale {n : ℕ}
    (b : Aux (n + 1) → ℝ → ℝ → ℂ) (h : ℝ × ℝ → ℂ)
    (R c : ℝ) {δ : ℝ} (hδ : 0 < δ) (w : Aux (n + 1)) :
    timeSliceExtension (fun x : Aux (n + 1) × ℝ => jetPolynomial x.1 x.2)
      (fun x => b x.1 x.2.1 x.2.2) h R c δ w =
      δ • polynomialExtension (rescaledMomentAmplitude b c δ hδ.ne')
        (fun x => h (c + δ * x.1, x.2)) (R * δ ^ n)
          (momentParabolicMap n c δ hδ.ne' w) := by
  unfold timeSliceExtension polynomialExtension
  conv_lhs => arg 2; ext η; rw [integral_time_affine _ c hδ]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  apply congrArg (fun z : ℂ => δ • z)
  apply integral_congr_ae
  filter_upwards [] with t
  have ht : (c + δ * t - c) / δ = t := by field_simp; ring
  simp only [rescaledMomentAmplitude,
    ContinuousLinearEquiv.symm_apply_apply, ht, phaseOscillation]
  rw [jetPolynomial_parabolic_rescale w c δ t hδ.ne']
  have hp : (R : ℂ) * η * (δ ^ n * jetPolynomial (momentParabolicMap n c δ hδ.ne' w) t) =
      (R * δ ^ n) * η * jetPolynomial (momentParabolicMap n c δ hδ.ne' w) t := by ring
  push_cast
  rw [hp]
  ring

theorem lintegral_momentParabolicMap_image {n : ℕ}
    {K : Set (Aux (n + 1))} (hK : MeasurableSet K)
    (c δ : ℝ) (hδ : δ ≠ 0) (F : Aux (n + 1) → ℝ≥0∞) :
    (∫⁻ y in momentParabolicMap n c δ hδ '' K, F y) =
      ENNReal.ofReal (|δ⁻¹| ^ (n * (n + 1) / 2)) *
        ∫⁻ x in K, F (momentParabolicMap n c δ hδ x) := by
  let L := momentParabolicMap n c δ hδ
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK
    (f' := fun _ => L.toContinuousLinearMap)
    (fun _ _ => L.hasFDerivAt.hasFDerivWithinAt) L.injective.injOn F]
  change (∫⁻ x in K, ENNReal.ofReal |LinearMap.det L.toLinearMap| * F (L x)) = _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [det_momentParabolicMap_eq, abs_pow]

theorem eLpNorm_momentParabolicMap_image {n : ℕ}
    {K : Set (Aux (n + 1))} (hK : MeasurableSet K)
    (c δ : ℝ) (hδ : δ ≠ 0) (F : Aux (n + 1) → ℂ)
    (p : ℝ≥0∞) (hp : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm F p (volume.restrict (momentParabolicMap n c δ hδ '' K)) =
      ENNReal.ofReal (|δ⁻¹| ^ (n * (n + 1) / 2)) ^ (1 / p.toReal) *
        eLpNorm (fun x => F (momentParabolicMap n c δ hδ x)) p (volume.restrict K) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt,
    lintegral_momentParabolicMap_image hK, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

/-- The original time piece and the rescaled extension have exactly the
same norm after both Jacobian factors have been included. -/
theorem timeSliceExtension_moment_eLpNorm_rescale {n : ℕ}
    {K : Set (Aux (n + 1))} (hK : MeasurableSet K)
    (b : Aux (n + 1) → ℝ → ℝ → ℂ) (h : ℝ × ℝ → ℂ)
    (R c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (p : ℝ≥0∞) (hp : p ≠ 0) (hpt : p ≠ ∞) :
    ENNReal.ofReal (|δ⁻¹| ^ (n * (n + 1) / 2)) ^ (1 / p.toReal) *
      eLpNorm (timeSliceExtension (fun x : Aux (n + 1) × ℝ => jetPolynomial x.1 x.2)
        (fun x => b x.1 x.2.1 x.2.2) h R c δ) p (volume.restrict K) =
      ENNReal.ofReal δ * eLpNorm
        (polynomialExtension (rescaledMomentAmplitude b c δ hδ.ne')
          (fun x => h (c + δ * x.1, x.2)) (R * δ ^ n)) p
        (volume.restrict (momentParabolicMap n c δ hδ.ne' '' K)) := by
  rw [eLpNorm_momentParabolicMap_image hK c δ hδ.ne' _ p hp hpt]
  have he := funext (timeSliceExtension_moment_rescale b h R c hδ)
  rw [he]
  change _ * eLpNorm (δ • (fun w => polynomialExtension
    (rescaledMomentAmplitude b c δ hδ.ne') (fun x => h (c + δ * x.1, x.2))
      (R * δ ^ n) (momentParabolicMap n c δ hδ.ne' w))) p (volume.restrict K) = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hδ.le]
  ac_rfl

end PlanarNikodym
