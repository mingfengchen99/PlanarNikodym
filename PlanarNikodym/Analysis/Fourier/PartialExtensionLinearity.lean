import PlanarNikodym.Analysis.Fourier.PartialExtensionLInfinity

/-! Actual L¹-domain linearity of the partial Fourier main operator.
These identities justify decomposing the input by amplitude truncation. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem planeFourierIntegral_add {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ξ : Plane) :
    planeFourierIntegral (f + g) ξ = planeFourierIntegral f ξ + planeFourierIntegral g ξ := by
  simp only [planeFourierIntegral, Pi.add_apply, add_mul]
  exact integral_add (planeFourierIntegrand_integrable hf ξ) (planeFourierIntegrand_integrable hg ξ)

theorem planeFourierIntegral_const_smul (c : ℂ) (f : Plane → ℂ) (ξ : Plane) :
    planeFourierIntegral (c • f) ξ = c * planeFourierIntegral f ξ := by
  simp only [planeFourierIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem Family.cutoffPartialExtension_eq_fourierIntegral {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (q : Parameters 2 d) :
    G.cutoffPartialExtension χ L β r f q =
      r ^ 2 • ∫ ξ : Plane, ((L.bandSymbol 0 ξ * β ξ.2 : ℝ) : ℂ) *
        planeFourierIntegral f (r • ξ) * G.cutoffOscillatoryAmplitude χ q (r • ξ) := by
  unfold Family.cutoffPartialExtension
  congr 1
  exact (G.weighted_scaled_cutoffOscillatoryIntegral_eq_partialExtension χ hχ hc hγ
    _ ((L.bandSymbol_smooth 0).continuous.mul (hβ.comp continuous_snd))
    (L.bandSymbol_compact 0).mul_right hf q r).symm

theorem Family.cutoffPartialExtension_add {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    G.cutoffPartialExtension χ L β r (f + g) =
      G.cutoffPartialExtension χ L β r f + G.cutoffPartialExtension χ L β r g := by
  funext q
  simp only [Pi.add_apply]
  rw [G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L β hβ (hf.add hg),
    G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L β hβ hf,
    G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L β hβ hg]
  simp_rw [planeFourierIntegral_add hf hg, mul_add, add_mul]
  have hm : Continuous (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) :=
    (L.bandSymbol_smooth 0).continuous.mul (hβ.comp continuous_snd)
  rw [integral_add
    (G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hc hγ
      (weighted_scaledFourierData_integrable hm (L.bandSymbol_compact 0).mul_right hf r) q r)
    (G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hc hγ
      (weighted_scaledFourierData_integrable hm (L.bandSymbol_compact 0).mul_right hg r) q r),
    smul_add]

theorem Family.cutoffPartialExtension_const_smul {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (c : ℂ) (r : ℝ) :
    G.cutoffPartialExtension χ L β r (c • f) = c • G.cutoffPartialExtension χ L β r f := by
  funext q
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L β hβ (hf.smul c),
    G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L β hβ hf]
  simp_rw [planeFourierIntegral_const_smul]
  rw [show (fun ξ : Plane => ((L.bandSymbol 0 ξ * β ξ.2 : ℝ) : ℂ) *
      (c * planeFourierIntegral f (r • ξ)) * G.cutoffOscillatoryAmplitude χ q (r • ξ)) =
      fun ξ => c * (((L.bandSymbol 0 ξ * β ξ.2 : ℝ) : ℂ) *
        planeFourierIntegral f (r • ξ) * G.cutoffOscillatoryAmplitude χ q (r • ξ)) by
      funext ξ; ring,
    integral_const_mul, mul_smul_comm]

end PlanarNikodym
