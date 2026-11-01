import PlanarNikodym.Analysis.Jets.ScalarJetWeightedRepresentation

/-! The same fixed microlocal split works for every finite vertical jet.
Polynomial frequency weights introduce no additional error support. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem scalarJet_weighted_error_support (L : FrequencyCutoff)
    (β : ℝ → ℝ) (m : ℕ) :
    tsupport (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ * (1 - β ξ.2)) ⊆
      tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)) := by
  simp only [mul_assoc]
  exact tsupport_mul_subset_right

/-- A specified nonstationary split automatically controls every actual
normalized derivative symbol. The constant precedes scale and input. -/
theorem Family.exists_scalarJet_weighted_error_decay {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hne : ∀ ξ ∈ tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)),
      ∀ x ∈ tsupport χ, deriv (G.graphPhase x.2 ξ) x.1 ≠ 0)
    (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
      eLpNorm (G.cutoffFrequencyError χ
        (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ * (1 - β ξ.2)) r f) p volume ≤
          ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  apply G.exists_uniform_nonstationary_error_Lp_decay χ hχ hcχ hγ _
    (((contDiff_snd.pow m).mul (L.bandSymbol_smooth 0)).mul
      (contDiff_const.sub (hβ.comp contDiff_snd)))
    ((L.bandSymbol_compact 0).mul_left.mul_right) _ p hp N
  exact fun ξ hξ x hx => hne ξ (scalarJet_weighted_error_support L β m hξ) x hx

/-- The microlocal cutoff is chosen before every jet order, integrability
exponent, decay order, frequency and input. -/
theorem Family.exists_scalarJet_microlocal_error_decay {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) :
    ∃ (δ : ℝ) (β : ℝ → ℝ), 0 < δ ∧ δ ≤ 1 / 4 ∧ ContDiff ℝ ∞ β ∧
      (∀ s, 0 ≤ β s ∧ β s ≤ 1) ∧
      (∀ s, |s| ≤ δ / 2 → β s = 0) ∧ (∀ s, δ ≤ |s| → β s = 1) ∧
      ∀ (m : ℕ) (p : ℝ≥0∞), 1 ≤ p → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
          eLpNorm (G.cutoffFrequencyError χ
            (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ * (1 - β ξ.2)) r f) p volume ≤
              ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  obtain ⟨δ, β, hδ, hδle, hβ, hβbound, hβzero, hβone, _, _, _, hnonstat⟩ :=
    G.exists_microlocal_band_split χ hcχ hγ L
  refine ⟨δ, β, hδ, hδle, hβ, hβbound, hβzero, hβone, ?_⟩
  intro m p hp N
  apply G.exists_scalarJet_weighted_error_decay χ hχ hcχ hγ L β hβ _ m p hp N
  intro ξ hξ x hx hz
  have h := hnonstat ξ hξ x hx
  simp only [hz, abs_zero] at h
  linarith

end PlanarNikodym
