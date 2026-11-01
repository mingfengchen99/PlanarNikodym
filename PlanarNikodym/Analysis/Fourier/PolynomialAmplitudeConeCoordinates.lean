import PlanarNikodym.Analysis.Fourier.PolynomialConeCoordinates
import PlanarNikodym.Analysis.Fourier.JointAmplitudeFourier

/-! Exact identification of the last-stage polynomial extension with the
actual planar cone operator including its variable amplitude. -/
noncomputable section
open MeasureTheory
namespace PlanarNikodym

/-- The real two-coefficient polynomial extension is the amplitude cone
operator; the Fourier frequency conversion remains exactly `2π r`. -/
theorem polynomialExtension_one_eq_amplitudeConeExtension
    (b : Aux 2 → ℝ → ℝ → ℂ) (h : Plane → ℂ) (r : ℝ) (w : Aux 2) :
    polynomialExtension b h (2 * Real.pi * r) w =
      amplitudeConeExtension
        (fun y x => b ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm y) x.1 x.2)
        h r (w 0, w 1) := by
  have he : (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (w 0, w 1) = w :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm_apply_apply w
  unfold polynomialExtension amplitudeConeExtension
  dsimp only
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [phaseOscillation_jetPolynomial_one]
  ring

end PlanarNikodym
