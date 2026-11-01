import PlanarNikodym.Analysis.Fourier.MicrolocalSplit

/-! Exact main/error decomposition of the actual band average. All three
frequency integrals are absolutely integrable; no error estimate is assumed. -/
noncomputable section
open Set MeasureTheory

namespace PlanarNikodym

theorem FrequencyCutoff.weighted_bandFrequencyData_integrable (L : FrequencyCutoff)
    (k : ℕ) {f : Plane → ℂ} (hf : Integrable f) (b : Plane → ℝ) (hb : Continuous b) :
    Integrable (fun ξ : Plane => ((L.bandSymbol k ξ * b ξ : ℝ) : ℂ) * planeFourierIntegral f ξ) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp ((L.bandSymbol_smooth k).continuous.mul hb)).mul
      (continuous_planeFourierIntegral hf)
  · exact (((L.bandSymbol_compact k).mul_right).comp_left (g := Complex.ofRealCLM) rfl).mul_right

/-- The vertical cutoff is evaluated at the normalized frequency `2⁻ᵏξ₂`.
The identity therefore uses the same fixed cutoff at every frequency scale. -/
theorem Family.cutoffAverage_band_eq_split_oscillatoryIntegral {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (β : ℝ → ℝ) (hβ : Continuous β) {f : Plane → ℂ} (hf : Integrable f)
    (k : ℕ) (q : Parameters 2 d) :
    G.cutoffAverage χ (L.band k f) q =
      (∫ ξ : Plane, ((L.bandSymbol k ξ * β (((2 : ℝ) ^ k)⁻¹ * ξ.2) : ℝ) : ℂ) *
        planeFourierIntegral f ξ * G.cutoffOscillatoryAmplitude χ q ξ) +
      ∫ ξ : Plane, ((L.bandSymbol k ξ * (1 - β (((2 : ℝ) ^ k)⁻¹ * ξ.2)) : ℝ) : ℂ) *
        planeFourierIntegral f ξ * G.cutoffOscillatoryAmplitude χ q ξ := by
  let b : Plane → ℝ := fun ξ => β (((2 : ℝ) ^ k)⁻¹ * ξ.2)
  have hb : Continuous b := hβ.comp (continuous_const.mul continuous_snd)
  have hm := L.weighted_bandFrequencyData_integrable k hf b hb
  have he := L.weighted_bandFrequencyData_integrable k hf (fun ξ => 1 - b ξ) (continuous_const.sub hb)
  have hmi := G.cutoffOscillatoryAmplitude_mul_integrable χ hχ hc hγ hm q
  have hei := G.cutoffOscillatoryAmplitude_mul_integrable χ hχ hc hγ he q
  rw [G.cutoffAverage_band_eq_oscillatoryIntegral χ L hχ hc hγ hf k q]
  rw [← integral_add hmi hei]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [b, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

end PlanarNikodym
