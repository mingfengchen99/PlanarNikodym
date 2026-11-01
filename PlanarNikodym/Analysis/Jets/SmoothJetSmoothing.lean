import PlanarNikodym.Analysis.Jets.SmoothScalarWeightedSmoothing
import PlanarNikodym.Analysis.Jets.ScalarJetSmoothing
import PlanarNikodym.Analysis.Localization.JetLocalization

/-! Actual finite auxiliary-jet smoothing for genuinely C∞ cinematic
phases in every auxiliary dimension. The scalar weighted theorem is
proved for the original operator and all differentiated amplitudes. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

theorem Family.exists_smooth_jet_smoothing_neighborhood {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (x : ℝ × Parameters 2 d) (hd : G.cinematicDet x ≠ 0) :
    ∃ O : Set (ℝ × Parameters 2 d), IsOpen O ∧ x ∈ O ∧
      ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∀ (L : FrequencyCutoff) (p : ℝ≥0), smoothingThreshold d ≤ p →
      ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → JetSmoothingInput G χ L p s ε := by
  obtain ⟨O, hO, hx, _hreg, hscalar⟩ :=
    G.exists_smooth_scalar_weighted_smoothing_neighborhood hG x hd
  refine ⟨O, hO, hx, ?_⟩
  intro χ hχ hc hs L p hp s ε hε
  apply G.jetSmoothingInput_of_scalarJet_estimates χ hχ hc
    (fun _ _ => hG.contDiffAt) L p ((smoothingThreshold_one_le d).trans hp) s ε
  intro ψ hψ hcψ hsψ m
  exact hscalar ψ hψ hcψ (hsψ.trans hs) L p hp ε hε m

theorem Family.smooth_jetSmoothingInput_of_cinematic_support {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    (s : ℕ) {ε : ℝ} (hε : 0 < ε) : JetSmoothingInput G χ L p s ε := by
  apply jetSmoothingInput_of_local_cutoffs G χ hχ hc hχ0
    (fun _ _ => hG.contDiffAt) L p ((smoothingThreshold_one_le d).trans hp) s ε
  intro x hx
  obtain ⟨O, hO, hxO, h⟩ := G.exists_smooth_jet_smoothing_neighborhood hG x (hd x hx)
  exact ⟨O, hO, hxO, fun ψ hψ hcψ hsψ => h ψ hψ hcψ hsψ L p hp s ε hε⟩

theorem Family.theorem_2_1_smooth_of_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffAverage χ (L.band k f)) p volume ≤
        C * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k * eLpNorm f p volume :=
  theorem_2_1_of_jet_smoothing G χ L p 0 ε
    (G.smooth_jetSmoothingInput_of_cinematic_support hG χ hχ hc hχ0 hd L p hp 0 hε)

end PlanarNikodym
