import PlanarNikodym.Analysis.Fourier.LinearConeAmplitudeL2
import PlanarNikodym.Analysis.Fourier.ConeOutputDilation
import PlanarNikodym.Analysis.Fourier.UniformAmplitudeFourier

/-! The degree-one phase in fixed, unscaled output coordinates.  The
amplitude remains in those fixed coordinates while the true output
Jacobian contributes `δ⁻¹` to the squared L² estimate. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

def dilatedAmplitudeConeExtension (b : Plane → Plane → ℂ) (h : Plane → ℂ)
    (r δ : ℝ) (w : Plane) : ℂ :=
  ∫ η : ℝ, ∫ τ : ℝ, b w (τ, η) * h (τ, η) *
    planeFourierCharacter (r • coneOutputDilation δ w) (η, η * τ)

theorem dilatedAmplitudeConeExtension_eq_fourier_superposition
    (b : SchwartzMap (Plane × Plane) ℂ) {h : Plane → ℂ}
    (hh : Integrable h) (r δ : ℝ) (w : Plane) :
    dilatedAmplitudeConeExtension (fun w x => b (w, x)) h r δ w =
      ∫ ζ : AmplitudeFourierSpace, jointAmplitudeFourier b ζ *
        planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
        linearConeExtension (modulatedConeData h (amplitudeFourierEquiv ζ).2) r
          (coneOutputDilation δ w) := by
  have hi : Integrable (fun x : Plane => b (w, x) * h x *
      planeFourierCharacter (r • coneOutputDilation δ w) (x.2, x.2 * x.1)) :=
    (hh.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 b)
      (b.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun x => b.norm_le_seminorm ℝ (w, x))).mul_bdd (c := 1)
      (continuous_planeFourierCharacter.comp (continuous_const.prodMk
        (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun _ => by simp)
  have he := amplitudeConeIntegral_eq_fourier_superposition b hh r w (coneOutputDilation δ w)
  rw [Measure.volume_eq_prod, integral_prod_symm _ hi] at he
  exact he

def dilatedModulatedConeOutput (h : Plane → ℂ) (r δ : ℝ)
    (ζ : AmplitudeFourierSpace) (w : Plane) : ℂ :=
  planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
    modulatedConeValue h r ((amplitudeFourierEquiv ζ).2, coneOutputDilation δ w)

theorem continuous_dilatedModulatedConeOutput {h : Plane → ℂ}
    (h1 : Integrable h) (r δ : ℝ) :
    Continuous (Function.uncurry (dilatedModulatedConeOutput h r δ)) := by
  have hM : Continuous (fun p : AmplitudeFourierSpace × Plane =>
      ((amplitudeFourierEquiv p.1).2, coneOutputDilation δ p.2)) :=
    (continuous_snd.comp (amplitudeFourierEquiv.continuous.comp continuous_fst)).prodMk
      (by unfold coneOutputDilation; fun_prop)
  have hV : Continuous (modulatedConeValue h r) :=
    continuous_modulated_linearConeExtension h1 r
  have hL := hV.comp hM
  have hN : Continuous (fun p : AmplitudeFourierSpace × Plane =>
      planeFourierCharacter p.2 (amplitudeFourierEquiv p.1).1) :=
    continuous_planeFourierCharacter.comp
      (continuous_snd.prodMk (continuous_fst.comp
        (amplitudeFourierEquiv.continuous.comp continuous_fst)))
  exact hN.mul hL

theorem lintegral_dilatedModulatedConeOutput_sq_le (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume)
    {a r δ : ℝ} (ha : 0 < a) (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) (ζ : AmplitudeFourierSpace) :
    (∫⁻ w : Plane, ‖dilatedModulatedConeOutput h r δ ζ w‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal δ⁻¹ * (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) := by
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
  have hb := lintegral_linearConeExtension_dilated_sq_le_of_integrable
    g hg hg1 hg2 ha hr hδ hggap
  have he (x ξ : Plane) : ‖planeFourierCharacter x ξ‖ₑ = 1 := by
    rw [← ofReal_norm, norm_planeFourierCharacter, ENNReal.ofReal_one]
  simpa only [dilatedModulatedConeOutput, modulatedConeValue, g, modulatedConeData,
    enorm_mul, he, one_mul] using hb

theorem lintegral_dilatedAmplitudeConeExtension_sq_le
    (b : SchwartzMap (Plane × Plane) ℂ) (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume)
    {a r δ : ℝ} (ha : 0 < a) (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    (∫⁻ w : Plane, ‖dilatedAmplitudeConeExtension (fun w x => b (w, x)) h r δ w‖ₑ ^ (2 : ℕ)) ≤
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) ^ (2 : ℕ) *
        (ENNReal.ofReal δ⁻¹ * (ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) *
          ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ))) := by
  calc
    _ = ∫⁻ w : Plane, ‖∫ ζ : AmplitudeFourierSpace,
        jointAmplitudeFourier b ζ * dilatedModulatedConeOutput h r δ ζ w‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro w
      congr 2
      rw [dilatedAmplitudeConeExtension_eq_fourier_superposition b h1]
      apply integral_congr_ae
      filter_upwards [] with ζ
      change jointAmplitudeFourier b ζ * planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
          linearConeExtension (modulatedConeData h (amplitudeFourierEquiv ζ).2) r
            (coneOutputDilation δ w) =
        jointAmplitudeFourier b ζ * (planeFourierCharacter w (amplitudeFourierEquiv ζ).1 *
          linearConeExtension (modulatedConeData h (amplitudeFourierEquiv ζ).2) r
            (coneOutputDilation δ w))
      exact mul_assoc _ _ _
    _ ≤ _ := lintegral_enorm_sq_integral_superposition_le volume volume
      (jointAmplitudeFourier b) (dilatedModulatedConeOutput h r δ)
      (jointAmplitudeFourier b).continuous.measurable
      (continuous_dilatedModulatedConeOutput h1 r δ).measurable _
      (lintegral_dilatedModulatedConeOutput_sq_le h hh h1 h2 ha hr hδ hgap)

theorem eLpNorm_dilatedAmplitudeConeExtension_two_le
    (b : SchwartzMap (Plane × Plane) ℂ) (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume)
    {a r δ : ℝ} (ha : 0 < a) (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) :
    eLpNorm (dilatedAmplitudeConeExtension (fun w x => b (w, x)) h r δ) 2 volume ≤
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) *
        ENNReal.ofReal δ⁻¹ ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
            eLpNorm h 2 volume := by
  have he (g : Plane → ℂ) : eLpNorm g 2 volume =
      (∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (f := g) (μ := volume)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)))
  rw [he, he]
  have hb := ENNReal.rpow_le_rpow
    (lintegral_dilatedAmplitudeConeExtension_sq_le b h hh h1 h2 ha hr hδ hgap)
    (by norm_num : 0 ≤ 1 / (2 : ℝ))
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ 1 / (2 : ℝ))] at hb
  have hs (x : ℝ≥0∞) : (x ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) = x := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  simpa only [hs, mul_assoc] using hb

/-- Fixed support and mixed full-derivative bounds give one constant for
all frequencies, slices, dilations, and L¹∩L² data in the family. -/
theorem exists_uniform_dilatedAmplitudeConeExtension_two_bound
    {P : Type*} (S : P → SchwartzMap (Plane × Plane) ℂ)
    {K : Set (Plane × Plane)} (hK : IsCompact K)
    (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p (h : Plane → ℂ),
      Measurable h → Integrable h → MemLp h 2 volume →
      ∀ a r δ : ℝ, 0 < a → 0 < r → 0 < δ →
      (∀ x : Plane, |x.2| < a → h x = 0) →
      eLpNorm (dilatedAmplitudeConeExtension (fun w x => S p (w, x)) h r δ) 2 volume ≤
        ENNReal.ofReal C * ENNReal.ofReal δ⁻¹ ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal (a⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) *
            eLpNorm h 2 volume := by
  obtain ⟨C, hC, hcoef⟩ := exists_uniform_jointAmplitudeFourier_L1_bound S hK hs hjet
  refine ⟨C, hC, ?_⟩
  intro p h hh h1 h2 a r δ ha hr hδ hgap
  exact (eLpNorm_dilatedAmplitudeConeExtension_two_le (S p) h hh h1 h2 ha hr hδ hgap).trans
    (by gcongr; exact hcoef p)

end PlanarNikodym
