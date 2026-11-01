import PlanarNikodym.Analysis.Fourier.PartialExtensionLinearity
import PlanarNikodym.Analysis.Fourier.ReflectedFrequencyMain

/-! A smooth positive/negative radial partition of the actual multiplier.
The original main operator is exactly the sum of the two components. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym
set_option backward.isDefEq.respectTransparency false

def positiveRadialSymbol (κ : ℝ) (β : ℝ → ℝ) (η : ℝ) : ℝ :=
  β η * Real.smoothTransition (η / κ)

def negativeRadialSymbol (κ : ℝ) (β : ℝ → ℝ) (η : ℝ) : ℝ :=
  β η - positiveRadialSymbol κ β η

theorem contDiff_positiveRadialSymbol (κ : ℝ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (positiveRadialSymbol κ β) :=
  hβ.mul (Real.smoothTransition.contDiff.comp (contDiff_id.div_const κ))

theorem contDiff_negativeRadialSymbol (κ : ℝ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (negativeRadialSymbol κ β) :=
  hβ.sub (contDiff_positiveRadialSymbol κ hβ)

theorem positiveRadialSymbol_eq_zero {κ : ℝ} (hκ : 0 < κ) {β : ℝ → ℝ}
    (hgap : ∀ η : ℝ, |η| < κ → β η = 0) {η : ℝ} (hη : η < κ) :
    positiveRadialSymbol κ β η = 0 := by
  by_cases hz : η ≤ 0
  · rw [positiveRadialSymbol, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg hz hκ.le), mul_zero]
  · rw [positiveRadialSymbol, hgap η (by simpa only [abs_of_pos (lt_of_not_ge hz)] using hη),
      zero_mul]

theorem negativeRadialSymbol_eq_zero {κ : ℝ} (hκ : 0 < κ) {β : ℝ → ℝ}
    (hgap : ∀ η : ℝ, |η| < κ → β η = 0) {η : ℝ} (hη : -κ < η) :
    negativeRadialSymbol κ β η = 0 := by
  by_cases hh : κ ≤ η
  · rw [negativeRadialSymbol, positiveRadialSymbol,
      Real.smoothTransition.one_of_one_le ((le_div_iff₀ hκ).mpr (by simpa using hh)),
      mul_one, sub_self]
  · have hb : β η = 0 := hgap η (abs_lt.mpr ⟨hη, lt_of_not_ge hh⟩)
    simp only [negativeRadialSymbol, positiveRadialSymbol, hb, zero_mul, sub_self]

theorem Family.cutoffPartialExtension_add_verticalSymbol {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β₁ β₂ : ℝ → ℝ) (hβ₁ : Continuous β₁) (hβ₂ : Continuous β₂)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    G.cutoffPartialExtension χ L (β₁ + β₂) r f =
      G.cutoffPartialExtension χ L β₁ r f + G.cutoffPartialExtension χ L β₂ r f := by
  funext q
  simp only [Pi.add_apply]
  rw [G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L (β₁ + β₂) (hβ₁.add hβ₂) hf,
    G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L β₁ hβ₁ hf,
    G.cutoffPartialExtension_eq_fourierIntegral χ hχ hc hγ L β₂ hβ₂ hf]
  have h₁ := G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hc hγ
    (weighted_scaledFourierData_integrable
      ((L.bandSymbol_smooth 0).continuous.mul (hβ₁.comp continuous_snd))
      (L.bandSymbol_compact 0).mul_right hf r) q r
  have h₂ := G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hc hγ
    (weighted_scaledFourierData_integrable
      ((L.bandSymbol_smooth 0).continuous.mul (hβ₂.comp continuous_snd))
      (L.bandSymbol_compact 0).mul_right hf r) q r
  simp only [Pi.add_apply, mul_add, Complex.ofReal_add, add_mul]
  rw [← smul_add]
  congr 1
  exact integral_add h₁ h₂

theorem Family.cutoffPartialExtension_radial_split {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {f : Plane → ℂ} (hf : Integrable f) (κ r : ℝ) :
    G.cutoffPartialExtension χ L β r f =
      G.cutoffPartialExtension χ L (positiveRadialSymbol κ β) r f +
        G.cutoffPartialExtension χ L (negativeRadialSymbol κ β) r f := by
  have he : β = positiveRadialSymbol κ β + negativeRadialSymbol κ β := by
    funext η
    simp only [Pi.add_apply, negativeRadialSymbol, add_sub_cancel]
  conv_lhs => rw [he]
  exact G.cutoffPartialExtension_add_verticalSymbol χ hχ hc hγ L _ _
    (contDiff_positiveRadialSymbol κ hβ).continuous
    (contDiff_negativeRadialSymbol κ hβ).continuous hf r

end PlanarNikodym
