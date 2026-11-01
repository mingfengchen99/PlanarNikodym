import PlanarNikodym.Analysis.Jets.ScalarJetFourier

/-! Actual main/error decomposition for the frequency weights produced
by auxiliary differentiation. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlanarNikodym
set_option maxHeartbeats 800000

/-- The general normalized physical multiplier and the frequency-space
operator are the same actual curve average. -/
theorem Family.scalarJet_scaledFrequencyConvolution_eq_frequencyOperator {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℝ} (ha : Continuous a) (hc : HasCompactSupport a)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (q : Parameters 2 d) :
    G.cutoffAverage χ (scaledFrequencyConvolution a r f) q =
      G.cutoffFrequencyError χ a r f q := by
  unfold Family.cutoffAverage Family.cutoffFrequencyError
  simp_rw [scaledFrequencyConvolution_eq_fourierIntegral ha
    (ha.integrable_of_hasCompactSupport hc) hf r]
  simp_rw [mul_smul_comm]
  rw [integral_smul]
  congr 1
  calc
    _ = ∫ t : ℝ, ∫ ξ : Plane,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) (r • ξ)) *
          ((a ξ : ℂ) * planeFourierIntegral f (r • ξ)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      ring
    _ = ∫ ξ : Plane, ∫ t : ℝ,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) (r • ξ)) *
          ((a ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
      integral_integral_swap (G.integrable_scaled_cutoffOscillatoryProduct χ hχ hcχ hγ
        (weighted_scaledFourierData_integrable ha hc hf r) q r)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [Family.cutoffOscillatoryAmplitude, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring

/-- Every normalized vertical weight has precisely the same microlocal
split, with no change of the input and no reprojection of its dyadic band. -/
theorem Family.scalarJet_weighted_main_add_error {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (m : ℕ) (r : ℝ) (q : Parameters 2 d) :
    G.cutoffAverage χ (scaledFrequencyConvolution
        (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f) q =
      G.cutoffPartialExtension χ L (fun η => η ^ m * β η) r f q +
      G.cutoffFrequencyError χ
        (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ * (1 - β ξ.2)) r f q := by
  let a : Plane → ℝ := fun ξ => ξ.2 ^ m * L.bandSymbol 0 ξ
  let am : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * (ξ.2 ^ m * β ξ.2)
  let ae : Plane → ℝ := fun ξ => ξ.2 ^ m * L.bandSymbol 0 ξ * (1 - β ξ.2)
  have ha : Continuous a := (continuous_snd.pow m).mul (L.bandSymbol_smooth 0).continuous
  have hca : HasCompactSupport a := (L.bandSymbol_compact 0).mul_left
  have ham : Continuous am := (L.bandSymbol_smooth 0).continuous.mul
    ((continuous_snd.pow m).mul (hβ.comp continuous_snd))
  have hcam : HasCompactSupport am := (L.bandSymbol_compact 0).mul_right
  have hae : Continuous ae := ha.mul (continuous_const.sub (hβ.comp continuous_snd))
  have hcae : HasCompactSupport ae := hca.mul_right
  rw [G.scalarJet_scaledFrequencyConvolution_eq_frequencyOperator χ hχ hcχ hγ ha hca hf,
    G.cutoffPartialExtension_eq_scaledFrequencyConvolution χ hχ hcχ hγ L (fun η => η ^ m * β η)
      ((continuous_id.pow m).mul hβ) hf,
    G.scalarJet_scaledFrequencyConvolution_eq_frequencyOperator χ hχ hcχ hγ ham hcam hf]
  have hmi := G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hcχ hγ
    (weighted_scaledFourierData_integrable ham hcam hf r) q r
  have hei := G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hcχ hγ
    (weighted_scaledFourierData_integrable hae hcae hf r) q r
  unfold Family.cutoffFrequencyError
  rw [← smul_add, ← integral_add hmi hei]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  dsimp [a, am, ae]
  push_cast
  ring

end PlanarNikodym
