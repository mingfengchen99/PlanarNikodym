import PlanarNikodym.Analysis.Fourier.LinearConeL2
import PlanarNikodym.Analysis.Fourier.TimeSliceExtension

/-! The actual last-stage polynomial extension is the planar degree-one
cone operator, with the exact `2π` conversion and a measure-preserving
identification of its two coefficient coordinates. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem jetPolynomial_one (w : Aux 2) (τ : ℝ) :
    jetPolynomial w τ = w 0 + w 1 * τ := by
  simp [jetPolynomial, Fin.sum_univ_two]

theorem phaseOscillation_jetPolynomial_one (r τ η : ℝ) (w : Aux 2) :
    phaseOscillation (jetPolynomial w) ((2 * Real.pi * r) * η) τ =
      planeFourierCharacter (r • ((w 0, w 1) : Plane)) (η, η * τ) := by
  have he : ((2 * Real.pi * r) * η) * jetPolynomial w τ =
      2 * Real.pi * fourierPhase (r • ((w 0, w 1) : Plane)) (η, η * τ) := by
    rw [jetPolynomial_one]
    change (2 * Real.pi * r * η) * (w 0 + w 1 * τ) =
      2 * Real.pi * ((r * w 0) * η + (r * w 1) * (η * τ))
    ring
  unfold phaseOscillation planeFourierCharacter
  rw [he]

theorem polynomialExtension_one_eq_linearConeExtension (h : Plane → ℂ)
    (r : ℝ) (w : Aux 2) :
    polynomialExtension (n := 1) (fun _ _ _ => 1) h (2 * Real.pi * r) w =
      linearConeExtension h r (w 0, w 1) := by
  unfold polynomialExtension linearConeExtension
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [phaseOscillation_jetPolynomial_one]
  simp only [mul_one]
  exact mul_comm _ _

/-- No Jacobian is lost when passing from the two coefficient entries to
the planar model coordinates. -/
theorem eLpNorm_linearConeExtension_finTwo (h : Plane → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {a : ℝ} (ha : 0 < a)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) (r : ℝ) :
    eLpNorm (fun w : Aux 2 => linearConeExtension h r (w 0, w 1)) 2 volume =
      eLpNorm (linearConeExtension h r) 2 volume := by
  exact eLpNorm_comp_measurePreserving
    (continuous_linearConeExtension h hh hc ha hgap r).aestronglyMeasurable
    (volume_preserving_finTwoArrow ℝ)

/-- The actual degree-one polynomial extension has the `r⁻¹` L² bound
with uniform frequency-gap constant, before introducing the amplitude. -/
theorem eLpNorm_polynomialExtension_one_two_le (h : Plane → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    eLpNorm (polynomialExtension (n := 1) (fun _ _ _ => 1) h (2 * Real.pi * r)) 2 volume ≤
      ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) * eLpNorm h 2 volume := by
  have he : polynomialExtension (n := 1) (fun _ _ _ => 1) h (2 * Real.pi * r) =
      fun w : Aux 2 => linearConeExtension h r (w 0, w 1) :=
    funext (polynomialExtension_one_eq_linearConeExtension h r)
  rw [he, eLpNorm_linearConeExtension_finTwo h hh hc ha hgap r]
  exact eLpNorm_linearConeExtension_two_le h hh hc ha hr hgap

end PlanarNikodym
