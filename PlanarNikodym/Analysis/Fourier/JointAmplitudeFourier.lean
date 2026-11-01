import PlanarNikodym.Analysis.Fourier.ComplexSymbolKernels

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

/-- The actual cone extension with an output and input dependent amplitude. -/
def amplitudeConeExtension (b : Plane → Plane → ℂ) (h : Plane → ℂ)
    (r : ℝ) (w : Plane) : ℂ :=
  ∫ η : ℝ, ∫ τ : ℝ,
    b w (τ, η) * h (τ, η) * planeFourierCharacter (r • w) (η, η * τ)

/-- Euclidean Fourier coordinates for all four amplitude variables. -/
abbrev AmplitudeFourierSpace := WithLp 2 (FourierPlane × FourierPlane)

def amplitudeFourierEquiv : AmplitudeFourierSpace ≃L[ℝ] (Plane × Plane) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ FourierPlane FourierPlane).trans
    (fourierPlaneEquiv.prodCongr fourierPlaneEquiv)

/-- The actual joint Fourier coefficients of a Schwartz amplitude. -/
def jointAmplitudeFourier (b : SchwartzMap (Plane × Plane) ℂ) :
    SchwartzMap AmplitudeFourierSpace ℂ :=
  𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ amplitudeFourierEquiv b)

/-- Fourier inversion separates the actual amplitude into unit-modulus
characters of output and input, with an integrable Schwartz coefficient. -/
theorem jointAmplitudeFourier_reconstruction (b : SchwartzMap (Plane × Plane) ℂ)
    (w x : Plane) :
    b (w, x) = ∫ ζ : AmplitudeFourierSpace, jointAmplitudeFourier b ζ *
      planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
      planeFourierCharacter x (amplitudeFourierEquiv ζ).2 := by
  let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ amplitudeFourierEquiv b
  have h := congrArg (fun g : SchwartzMap AmplitudeFourierSpace ℂ =>
      g (amplitudeFourierEquiv.symm (w, x)))
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap AmplitudeFourierSpace ℂ) f)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
  change (∫ ζ : AmplitudeFourierSpace, _ ) = b (w, x) at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with ζ
  have hinner : inner ℝ ζ (amplitudeFourierEquiv.symm (w, x)) =
      fourierPhase w (amplitudeFourierEquiv ζ).1 +
      fourierPhase x (amplitudeFourierEquiv ζ).2 := by
    simp only [WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial,
      amplitudeFourierEquiv, fourierPlaneEquiv, fourierPhase,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      WithLp.prodContinuousLinearEquiv_apply]
    rfl
  change Complex.exp _ * jointAmplitudeFourier b ζ = _
  rw [hinner]
  unfold planeFourierCharacter
  have he : Complex.exp
      (((2 * Real.pi * (fourierPhase w (amplitudeFourierEquiv ζ).1 +
        fourierPhase x (amplitudeFourierEquiv ζ).2) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * fourierPhase w (amplitudeFourierEquiv ζ).1 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * fourierPhase x (amplitudeFourierEquiv ζ).2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

end PlanarNikodym
