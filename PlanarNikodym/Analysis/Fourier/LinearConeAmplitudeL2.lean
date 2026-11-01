import PlanarNikodym.Analysis.Fourier.AmplitudeConeRepresentation
import PlanarNikodym.Analysis.Fourier.IntegralSuperpositionL2
import PlanarNikodym.Analysis.Fourier.LinearConeIntegralL2
import PlanarNikodym.Analysis.Fourier.FourierCharacterJets

/-! Genuine L² bounds for the degree-one cone extension with a smooth
variable amplitude.  The constant is the L¹ norm of the explicitly
constructed joint Fourier coefficients of that amplitude. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

def modulatedConeData (h : Plane → ℂ) (q x : Plane) : ℂ :=
  planeFourierCharacter x q * h x

def modulatedConeValue (h : Plane → ℂ) (r : ℝ) (p : Plane × Plane) : ℂ :=
  linearConeExtension (modulatedConeData h p.1) r p.2

def modulatedConeOutput (h : Plane → ℂ) (r : ℝ)
    (ζ : AmplitudeFourierSpace) (w : Plane) : ℂ :=
  planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
    modulatedConeValue h r ((amplitudeFourierEquiv ζ).2, w)

theorem continuous_modulatedConeOutput {h : Plane → ℂ} (hi : Integrable h) (r : ℝ) :
    Continuous (Function.uncurry (modulatedConeOutput h r)) := by
  have hM : Continuous (fun p : AmplitudeFourierSpace × Plane =>
      ((amplitudeFourierEquiv p.1).2, p.2)) :=
    (continuous_snd.comp (amplitudeFourierEquiv.continuous.comp continuous_fst)).prodMk continuous_snd
  have hV : Continuous (modulatedConeValue h r) :=
    continuous_modulated_linearConeExtension hi r
  have hL := hV.comp hM
  have hN : Continuous (fun p : AmplitudeFourierSpace × Plane =>
      planeFourierCharacter p.2 (amplitudeFourierEquiv p.1).1) :=
    continuous_planeFourierCharacter.comp
      (continuous_snd.prodMk (continuous_fst.comp
        (amplitudeFourierEquiv.continuous.comp continuous_fst)))
  exact hN.mul hL

theorem lintegral_modulatedConeOutput_sq_le (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) (ζ : AmplitudeFourierSpace) :
    (∫⁻ w : Plane, ‖modulatedConeOutput h r ζ w‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  let g := modulatedConeData h (amplitudeFourierEquiv ζ).2
  have hg : Measurable g :=
    (planeFourierCharacter_contDiff _).continuous.measurable.mul hh
  have hg1 : Integrable g := h1.bdd_mul (c := 1)
    (planeFourierCharacter_contDiff _).continuous.aestronglyMeasurable
    (ae_of_all _ fun _ => by simp)
  have hg2 : MemLp g 2 volume := h2.congr_norm hg.aestronglyMeasurable
    (ae_of_all _ fun _ => by simp [g, modulatedConeData])
  have hggap : ∀ x : Plane, |x.2| < a → g x = 0 := by
    intro x hx
    simp only [g, modulatedConeData, hgap x hx, mul_zero]
  have hb := lintegral_linearConeExtension_sq_le_of_integrable g hg hg1 hg2 ha hr hggap
  have he (x ξ : Plane) : ‖planeFourierCharacter x ξ‖ₑ = 1 := by
    rw [← ofReal_norm, norm_planeFourierCharacter, ENNReal.ofReal_one]
  simpa only [modulatedConeOutput, modulatedConeValue, g, modulatedConeData,
    enorm_mul, he, one_mul] using hb

theorem lintegral_amplitudeConeExtension_sq_le
    (b : SchwartzMap (Plane × Plane) ℂ) (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ w : Plane, ‖amplitudeConeExtension (fun w x => b (w, x)) h r w‖ₑ ^ (2 : ℕ)) ≤
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) ^ (2 : ℕ) *
        (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) := by
  calc
    _ = ∫⁻ w : Plane, ‖∫ ζ : AmplitudeFourierSpace,
        jointAmplitudeFourier b ζ * modulatedConeOutput h r ζ w‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro w
      congr 2
      rw [amplitudeConeExtension_eq_fourier_superposition b h1]
      apply integral_congr_ae
      filter_upwards [] with ζ
      change jointAmplitudeFourier b ζ * planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
          linearConeExtension (fun x => planeFourierCharacter x (amplitudeFourierEquiv ζ).2 * h x) r w =
        jointAmplitudeFourier b ζ * (planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
          linearConeExtension (fun x => planeFourierCharacter x (amplitudeFourierEquiv ζ).2 * h x) r w)
      exact mul_assoc _ _ _
    _ ≤ _ := lintegral_enorm_sq_integral_superposition_le volume volume
      (jointAmplitudeFourier b) (modulatedConeOutput h r)
      (jointAmplitudeFourier b).continuous.measurable
      (continuous_modulatedConeOutput h1 r).measurable _
      (lintegral_modulatedConeOutput_sq_le h hh h1 h2 ha hr hgap)

/-- The actual variable-amplitude cone operator has the correct `r⁻¹`
L² decay.  Its coefficient constant is finite because it is a Schwartz
Fourier transform of the supplied amplitude. -/
theorem eLpNorm_amplitudeConeExtension_two_le
    (b : SchwartzMap (Plane × Plane) ℂ) (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    eLpNorm (amplitudeConeExtension (fun w x => b (w, x)) h r) 2 volume ≤
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) *
        ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
          eLpNorm h 2 volume := by
  have he (g : Plane → ℂ) : eLpNorm g 2 volume =
      (∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (f := g) (μ := volume)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)))
  rw [he, he]
  have hb := ENNReal.rpow_le_rpow (lintegral_amplitudeConeExtension_sq_le b h hh h1 h2 ha hr hgap)
    (by norm_num : 0 ≤ 1 / (2 : ℝ))
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ 1 / (2 : ℝ))] at hb
  have hs (x : ℝ≥0∞) : (x ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) = x := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  simpa only [hs, mul_assoc] using hb

theorem jointAmplitudeFourier_lintegral_enorm_lt_top
    (b : SchwartzMap (Plane × Plane) ℂ) :
    (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) < (∞ : ℝ≥0∞) :=
  (jointAmplitudeFourier b).integrable.hasFiniteIntegral

end PlanarNikodym
