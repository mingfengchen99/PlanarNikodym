import PlanarNikodym.Analysis.Fourier.MicrolocalErrorFrequencyDecay
import PlanarNikodym.Analysis.Fourier.CompactSymbolLpDecay
import PlanarNikodym.Analysis.Fourier.PartialFourierRepresentation

/-! Uniform physical-kernel bounds for the actual nonstationary error.
No frequency-derivative estimate or Fourier operator estimate is assumed. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal

namespace PlanarNikodym

/-- Actual nonstationary error kernels have arbitrary-order Lp decay,
uniformly in the curve parameters and the scale. This includes p = ∞. -/
theorem Family.exists_uniform_nonstationary_error_kernel_Lp_decay {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hne : ∀ ξ ∈ tsupport a, ∀ x ∈ tsupport χ,
      deriv (G.graphPhase x.2 ξ) x.1 ≠ 0)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q r, 1 ≤ r →
      eLpNorm (planeInverseFourierSchwartzCLM
        (G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r)) p volume ≤
          ENNReal.ofReal (C * (r⁻¹) ^ N) := by
  apply exists_uniform_complex_symbol_kernel_Lp_decay
    (fun q r => G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r)
    hca.isCompact
    (fun q r => G.tsupport_cutoffOscillatoryErrorSchwartz_subset χ hχ hcχ hγ a ha hca q r)
    _ p hp N
  intro j n
  obtain ⟨C, hC, hb⟩ :=
    G.exists_uniform_cutoffOscillatoryAmplitude_symbol_frequency_jet_decay
      χ hχ hcχ hγ a ha hca hne j n
  refine ⟨C, hC, ?_⟩
  intro q r hr ξ
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  simpa only [G.cutoffOscillatoryErrorSchwartz_coe, abs_of_pos hrpos] using
    hb q ξ r hrpos.ne'

/-- The actual error term in the rescaled band representation. -/
def Family.cutoffFrequencyError {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (a : Plane → ℝ) (r : ℝ) (f : Plane → ℂ) (q : Parameters 2 d) : ℂ :=
  r ^ 2 • ∫ ξ : Plane, (a ξ : ℂ) * planeFourierIntegral f (r • ξ) *
    G.cutoffOscillatoryAmplitude χ q (r • ξ)

theorem Family.cutoffFrequencyError_eq_scaledSymbolOperator {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (r : ℝ) (f : Plane → ℂ) (q : Parameters 2 d) :
    G.cutoffFrequencyError χ a r f q =
      scaledSymbolOperator (G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca q r) r f := by
  unfold cutoffFrequencyError scaledSymbolOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [G.cutoffOscillatoryErrorSchwartz_apply]
  ring

/-- Uniform arbitrary-order Lp decay of the actual nonstationary Fourier
operator. All symbol derivatives and compact parameter supports have been
proved from the original cutoff geometry. The constant precedes r and f. -/
theorem Family.exists_uniform_nonstationary_error_Lp_decay {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (a : Plane → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hne : ∀ ξ ∈ tsupport a, ∀ x ∈ tsupport χ,
      deriv (G.graphPhase x.2 ξ) x.1 ≠ 0)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
      eLpNorm (G.cutoffFrequencyError χ a r f) p volume ≤
        ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  let S := G.cutoffOscillatoryErrorSchwartz χ hχ hcχ hγ a ha hca
  have hdecay : ∀ j n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q r, 1 ≤ r →
      ∀ ξ, ‖iteratedFDeriv ℝ j (S q r) ξ‖ ≤ C * (r⁻¹) ^ n := by
    intro j n
    obtain ⟨C, hC, hb⟩ :=
      G.exists_uniform_cutoffOscillatoryAmplitude_symbol_frequency_jet_decay
        χ hχ hcχ hγ a ha hca hne j n
    refine ⟨C, hC, ?_⟩
    intro q r hr ξ
    have hrpos : 0 < r := zero_lt_one.trans_le hr
    simpa only [S, G.cutoffOscillatoryErrorSchwartz_coe, abs_of_pos hrpos] using
      hb q ξ r hrpos.ne'
  obtain ⟨C, hC, hb⟩ := exists_compact_symbol_operator_Lp_decay S hca.isCompact
    (fun q r => G.tsupport_cutoffOscillatoryErrorSchwartz_subset χ hχ hcχ hγ a ha hca q r)
    hdecay (hcχ.isCompact.image continuous_snd)
    (fun q hq r => G.cutoffOscillatoryErrorSchwartz_eq_zero_off_parameter_support
      χ hχ hcχ hγ a ha hca hq r) p hp N
  refine ⟨C, hC, ?_⟩
  intro r hr f hf
  have he : G.cutoffFrequencyError χ a r f =
      fun q => scaledSymbolOperator (S q r) r f := by
    funext q
    exact G.cutoffFrequencyError_eq_scaledSymbolOperator χ hχ hcχ hγ a ha hca r f q
  rw [he]
  exact hb r hr f hf

/-- A single cutoff built from the actual nonstationary region gives the
full scalar error estimate, at every p ≥ 1 (including ∞) and every decay
order. This is the error branch of the band decomposition. -/
theorem Family.exists_microlocal_error_Lp_decay {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) :
    ∃ (δ : ℝ) (β : ℝ → ℝ), 0 < δ ∧ δ ≤ 1 / 4 ∧ ContDiff ℝ ∞ β ∧
      (∀ s, 0 ≤ β s ∧ β s ≤ 1) ∧
      (∀ s, |s| ≤ δ / 2 → β s = 0) ∧ (∀ s, δ ≤ |s| → β s = 1) ∧
      ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
          eLpNorm (G.cutoffFrequencyError χ
            (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)) r f) p volume ≤
              ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  obtain ⟨δ, β, hδ, hδle, hβ, hβbound, hβzero, hβone, _, herror, _, hnonstat⟩ :=
    G.exists_microlocal_band_split χ hcχ hγ L
  refine ⟨δ, β, hδ, hδle, hβ, hβbound, hβzero, hβone, ?_⟩
  intro p hp N
  apply G.exists_uniform_nonstationary_error_Lp_decay χ hχ hcχ hγ _
    ((L.bandSymbol_smooth 0).mul (contDiff_const.sub (hβ.comp contDiff_snd))) herror _ p hp N
  intro ξ hξ x hx
  have h := hnonstat ξ hξ x hx
  intro hz
  simp only [hz, abs_zero] at h
  linarith

/-- The actual extension main term, retaining the complete normalized
frequency cutoff in its partial Fourier data. -/
def Family.cutoffPartialExtension {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (r : ℝ) (f : Plane → ℂ)
    (q : Parameters 2 d) : ℂ :=
  r ^ 2 • ∫ ξ₂ : ℝ, ∫ t : ℝ, (χ (t, q) : ℂ) *
    weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) f r t ξ₂ *
      oneDimFourierCharacter r (G.γ t q) ξ₂

theorem Family.cutoffAverage_band_sub_partialExtension_eq_error {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff)
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (β : ℝ → ℝ) (hβ : Continuous β) {f : Plane → ℂ} (hf : Integrable f)
    (k : ℕ) (q : Parameters 2 d) :
    G.cutoffAverage χ (L.band k f) q -
      G.cutoffPartialExtension χ L β ((2 : ℝ) ^ k) f q =
        G.cutoffFrequencyError χ (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2))
          ((2 : ℝ) ^ k) f q := by
  have h := G.cutoffAverage_band_eq_partialExtension_add_error χ L hχ hcχ hγ β hβ hf k q
  change G.cutoffAverage χ (L.band k f) q =
    G.cutoffPartialExtension χ L β ((2 : ℝ) ^ k) f q +
      G.cutoffFrequencyError χ (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2))
        ((2 : ℝ) ^ k) f q at h
  rw [h]
  abel

/-- The actual band average differs from its actual partial-Fourier main
term by an Lp error with any requested inverse dyadic power. This closes
the scalar error branch; it supplies no estimate for the main term. -/
theorem Family.exists_band_partialExtension_error_bound {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) :
    ∃ (δ : ℝ) (β : ℝ → ℝ), 0 < δ ∧ δ ≤ 1 / 4 ∧ ContDiff ℝ ∞ β ∧
      (∀ s, 0 ≤ β s ∧ β s ≤ 1) ∧
      (∀ s, |s| ≤ δ / 2 → β s = 0) ∧ (∀ s, δ ≤ |s| → β s = 1) ∧
      ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f →
          eLpNorm (fun q => G.cutoffAverage χ (L.band k f) q -
            G.cutoffPartialExtension χ L β ((2 : ℝ) ^ k) f q) p volume ≤
              ENNReal.ofReal (C * (((2 : ℝ) ^ k)⁻¹) ^ N) * eLpNorm f p volume := by
  obtain ⟨δ, β, hδ, hδle, hβ, hβbound, hβzero, hβone, hb⟩ :=
    G.exists_microlocal_error_Lp_decay χ hχ hcχ hγ L
  refine ⟨δ, β, hδ, hδle, hβ, hβbound, hβzero, hβone, ?_⟩
  intro p hp N
  obtain ⟨C, hC, hc⟩ := hb p hp N
  refine ⟨C, hC, ?_⟩
  intro k f hf
  have he : (fun q => G.cutoffAverage χ (L.band k f) q -
      G.cutoffPartialExtension χ L β ((2 : ℝ) ^ k) f q) =
      G.cutoffFrequencyError χ (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2))
        ((2 : ℝ) ^ k) f := by
    funext q
    exact G.cutoffAverage_band_sub_partialExtension_eq_error χ L hχ.continuous hcχ
      (fun x hx => (hγ x hx).continuousAt) β hβ.continuous hf k q
  rw [he]
  exact hc ((2 : ℝ) ^ k) (one_le_pow₀ (by norm_num)) f hf

end PlanarNikodym
