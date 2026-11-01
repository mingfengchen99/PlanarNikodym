import PlanarNikodym.Analysis.Fourier.ConeFrequencyCoordinates
import PlanarNikodym.Analysis.Fourier.ComplexSymbolKernels

/-! The degree-one cone extension is the actual planar inverse Fourier
transform after the input frequency change `(τ,η) ↦ (η,ητ)`. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

def linearConeExtension (h : Plane → ℂ) (r : ℝ) (w : Plane) : ℂ :=
  ∫ η : ℝ, ∫ τ : ℝ, h (τ, η) * planeFourierCharacter (r • w) (η, η * τ)

/-- Exact input substitution at every nonzero vertical frequency. -/
theorem integral_coneFrequencyData_slice (h : Plane → ℂ) (F : Plane → ℂ)
    {η : ℝ} (hη : η ≠ 0) :
    (∫ ν : ℝ, coneFrequencyData h (η, ν) * F (η, ν)) =
      ∫ τ : ℝ, h (τ, η) * F (η, η * τ) := by
  let G : ℝ → ℂ := fun ν => h (ν / η, η) * F (η, ν)
  calc
    _ = |η|⁻¹ • ∫ ν : ℝ, G ν := by
      simp only [coneFrequencyData, coneFrequencyInverse, smul_mul_assoc,
        ← integral_smul, G]
    _ = ∫ τ : ℝ, G (η * τ) := by
      rw [Measure.integral_comp_mul_left, abs_inv]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with τ
      dsimp only [G]
      rw [mul_div_cancel_left₀ τ hη]

/-- Exact inverse Fourier representation for the smooth compact data
actually used in a frequency-separated time slice. -/
theorem linearConeExtension_eq_inverseFourierSchwartz
    (h : Plane → ℂ) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    {a : ℝ} (ha : 0 < a) (hgap : ∀ x : Plane, |x.2| < a → h x = 0)
    (r : ℝ) (w : Plane) :
    linearConeExtension h r w =
      planeInverseFourierSchwartzCLM (coneFrequencySchwartz h hh hc ha hgap) (r • w) := by
  let k := coneFrequencySchwartz h hh hc ha hgap
  have hki : Integrable (fun ξ : Plane => k ξ * planeFourierCharacter (r • w) ξ) :=
    k.integrable.mul_bdd (c := 1) (continuous_planeFourierCharacter.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => by simp))
  rw [planeInverseFourierSchwartzCLM_apply, Measure.volume_eq_prod,
    integral_prod _ hki]
  unfold linearConeExtension
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with η hη
  exact (integral_coneFrequencyData_slice h (planeFourierCharacter (r • w)) hη).symm

end PlanarNikodym
