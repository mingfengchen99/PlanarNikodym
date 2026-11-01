import PlanarNikodym.Analysis.Jets.ScalarJetExpansion
import PlanarNikodym.Analysis.Fourier.FourierCharacterJets
import PlanarNikodym.Analysis.Fourier.PartialExtensionLInfinity

/-! Exact vertical derivatives of the original dyadic multiplier. The
normalised frequency power stays in a fixed symbol, while the entire
frequency growth is the explicit factor `(2π i r)^m`. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace PlanarNikodym

private theorem continuous_scalarJet_fourierExponent :
    Continuous (fourierCharacterExponent : Plane → Plane →L[ℝ] ℂ) := by
  unfold fourierCharacterExponent fourierPhaseCLM
  fun_prop

/-- Compact frequency support justifies differentiation of the actual
Fourier integral even when its frequency density is merely continuous. -/
theorem hasFDerivAt_scalarJet_fourierIntegral {A : Plane → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) (r : ℝ) (x : Plane) :
    HasFDerivAt (fun z => ∫ ξ : Plane, A ξ * planeFourierCharacter z (r • ξ))
      (∫ ξ : Plane, A ξ • (planeFourierCharacter x (r • ξ) •
        fourierCharacterExponent (r • ξ))) x := by
  have hE : Continuous (fun ξ : Plane => fourierCharacterExponent (r • ξ)) :=
    continuous_scalarJet_fourierExponent.comp ((continuous_const (y := r)).smul continuous_id)
  have hchar (z : Plane) : Continuous (fun ξ : Plane => planeFourierCharacter z (r • ξ)) :=
    continuous_planeFourierCharacter.comp
      (continuous_const.prodMk (continuous_const.smul continuous_id))
  have hi (z : Plane) : Integrable (fun ξ => A ξ * planeFourierCharacter z (r • ξ)) :=
    (hA.mul (hchar z)).integrable_of_hasCompactSupport hc.mul_right
  have hdi (z : Plane) : Integrable (fun ξ => A ξ •
      (planeFourierCharacter z (r • ξ) • fourierCharacterExponent (r • ξ))) :=
    (hA.smul ((hchar z).smul hE)).integrable_of_hasCompactSupport hc.smul_right
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun z ξ => A ξ • (planeFourierCharacter z (r • ξ) •
      fourierCharacterExponent (r • ξ))) (s := univ)
    (bound := fun ξ => ‖A ξ‖ * ‖fourierCharacterExponent (r • ξ)‖)
    Filter.univ_mem (Eventually.of_forall fun z => (hi z).aestronglyMeasurable)
    (hi x) (hdi x).aestronglyMeasurable
  · filter_upwards [] with ξ z _
    simp only [norm_smul, norm_planeFourierCharacter, one_mul, le_refl]
  · exact (hA.norm.mul hE.norm).integrable_of_hasCompactSupport hc.norm.mul_right
  · filter_upwards [] with ξ z _
    simpa only [fourierCharacterExponent_apply, Pi.smul_def, Pi.smul_apply, smul_eq_mul, planeFourierCharacter] using
      ((fourierCharacterExponent (r • ξ)).hasFDerivAt.cexp.const_smul (A ξ))

/-- One vertical derivative multiplies the normalized frequency density
by `ξ₂` and contributes the precise scale and Fourier normalization. -/
theorem scalarJetVertical_fourierIntegral {A : Plane → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) (r : ℝ) :
    scalarJetVertical (fun z => ∫ ξ : Plane, A ξ * planeFourierCharacter z (r • ξ)) =
      fun z => (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I) *
        ∫ ξ : Plane, ((ξ.2 : ℂ) * A ξ) * planeFourierCharacter z (r • ξ) := by
  funext x
  unfold scalarJetVertical
  rw [(hasFDerivAt_scalarJet_fourierIntegral hA hc r x).fderiv]
  have hi : Integrable (fun ξ : Plane => A ξ •
      (planeFourierCharacter x (r • ξ) • fourierCharacterExponent (r • ξ))) := by
    apply (hA.smul ((continuous_planeFourierCharacter.comp
      (continuous_const.prodMk (continuous_const.smul continuous_id))).smul
        (continuous_scalarJet_fourierExponent.comp
          (continuous_const.smul continuous_id)))).integrable_of_hasCompactSupport
    exact hc.smul_right
  rw [ContinuousLinearMap.integral_apply hi (0, 1), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [smul_apply, smul_eq_mul, fourierCharacterExponent_apply,
    fourierPhase, Prod.smul_fst, Prod.smul_snd, zero_mul, one_mul, zero_add,
    Complex.ofReal_mul]
  ring

theorem scalarJetVertical_const_mul (c : ℂ) {f : Plane → ℂ}
    (hf : Differentiable ℝ f) :
    scalarJetVertical (fun x => c * f x) = fun x => c * scalarJetVertical f x := by
  funext x
  exact congrArg (fun D : Plane →L[ℝ] ℂ => D (0, 1))
    ((hf x).hasFDerivAt.const_mul c).fderiv

/-- All actual vertical derivatives of a compact frequency integral. -/
theorem scalarJetVerticalIter_fourierIntegral {A : Plane → ℂ}
    (hA : Continuous A) (hc : HasCompactSupport A) (m : ℕ) (r : ℝ) :
    scalarJetVerticalIter m (fun z => ∫ ξ : Plane, A ξ * planeFourierCharacter z (r • ξ)) =
      fun z => (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I) ^ m *
        ∫ ξ : Plane, ((ξ.2 : ℂ) ^ m * A ξ) * planeFourierCharacter z (r • ξ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hAm : Continuous (fun ξ : Plane => (ξ.2 : ℂ) ^ m * A ξ) :=
      ((Complex.continuous_ofReal.comp continuous_snd).pow m).mul hA
    have hcm : HasCompactSupport (fun ξ : Plane => (ξ.2 : ℂ) ^ m * A ξ) := hc.mul_left
    rw [scalarJetVerticalIter_succ, ih,
      scalarJetVertical_const_mul _ (fun x =>
        (hasFDerivAt_scalarJet_fourierIntegral hAm hcm r x).differentiableAt),
      scalarJetVertical_fourierIntegral hAm hcm r]
    funext x
    rw [pow_succ]
    have he : (fun ξ : Plane => (ξ.2 : ℂ) * ((ξ.2 : ℂ) ^ m * A ξ) *
        planeFourierCharacter x (r • ξ)) =
        fun ξ => (ξ.2 : ℂ) ^ (m + 1) * A ξ * planeFourierCharacter x (r • ξ) := by
      funext ξ
      rw [pow_succ]
      ring
    dsimp only
    rw [he]
    ring

/-- Actual derivatives of a fixed normalized multiplier; all scale growth
is explicit and the input remains unchanged. -/
theorem scalarJetVerticalIter_scaledFrequencyConvolution
    {a : Plane → ℝ} (ha : Continuous a) (hc : HasCompactSupport a)
    {f : Plane → ℂ} (hf : Integrable f) (m : ℕ) (r : ℝ) :
    scalarJetVerticalIter m (scaledFrequencyConvolution a r f) =
      fun x => (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I) ^ m *
        scaledFrequencyConvolution (fun ξ : Plane => ξ.2 ^ m * a ξ) r f x := by
  let A : Plane → ℂ := fun ξ => ((r ^ 2 : ℝ) : ℂ) * (a ξ : ℂ) *
    planeFourierIntegral f (r • ξ)
  have hA : Continuous A := (continuous_const.mul
    (Complex.continuous_ofReal.comp ha)).mul
      ((continuous_planeFourierIntegral hf).comp (continuous_const.smul continuous_id))
  have hcA : HasCompactSupport A :=
    ((hc.comp_left (g := Complex.ofRealCLM) rfl).mul_left).mul_right
  have he : scaledFrequencyConvolution a r f =
      fun x => ∫ ξ : Plane, A ξ * planeFourierCharacter x (r • ξ) := by
    funext x
    rw [scaledFrequencyConvolution_eq_fourierIntegral ha
      (ha.integrable_of_hasCompactSupport hc) hf r x, Complex.real_smul,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp [A]
    ring
  rw [he, scalarJetVerticalIter_fourierIntegral hA hcA m r]
  funext x
  congr 1
  rw [scaledFrequencyConvolution_eq_fourierIntegral (m := fun ξ : Plane => ξ.2 ^ m * a ξ)
    ((continuous_snd.pow m).mul ha)
    (((continuous_snd.pow m).mul ha).integrable_of_hasCompactSupport hc.mul_left)
    hf r x, Complex.real_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  dsimp [A]
  push_cast
  ring

/-- Exact dyadic form used in the auxiliary-jet smoothing theorem. -/
theorem FrequencyCutoff.scalarJetVerticalIter_band (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) (m k : ℕ) :
    scalarJetVerticalIter m (L.band k f) =
      fun x => (((2 * Real.pi * (2 : ℝ) ^ k : ℝ) : ℂ) * Complex.I) ^ m *
        scaledFrequencyConvolution
          (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) ((2 : ℝ) ^ k) f x := by
  have he : L.band k f = scaledFrequencyConvolution (L.bandSymbol 0) ((2 : ℝ) ^ k) f := by
    funext x
    rw [L.band_eq_rescaled_fourierIntegral k hf x,
      scaledFrequencyConvolution_eq_fourierIntegral (L.bandSymbol_smooth 0).continuous
        ((L.bandSymbol_smooth 0).continuous.integrable_of_hasCompactSupport (L.bandSymbol_compact 0)) hf]
  rw [he]
  exact scalarJetVerticalIter_scaledFrequencyConvolution (L.bandSymbol_smooth 0).continuous
    (L.bandSymbol_compact 0) hf m _

end PlanarNikodym
