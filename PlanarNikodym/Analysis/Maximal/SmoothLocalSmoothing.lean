import PlanarNikodym.Analysis.Jets.SmoothJetSmoothing
import PlanarNikodym.Analysis.Maximal.SmoothAnalysisAuxTwo
import PlanarNikodym.Analysis.Sobolev.GeneralBandSobolev

/-! The original local-smoothing and high-frequency maximal conclusions
for genuinely smooth phases in every auxiliary dimension, including zero.
The neighborhood precedes arbitrary signed smooth compact cutoffs. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

theorem Family.exists_smooth_local_smoothing {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (x : ℝ × Parameters 2 d) (hd : G.cinematicDet x ≠ 0) :
    ∃ O : Set (ℝ × Parameters 2 d), IsOpen O ∧ x ∈ O ∧
      ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∀ (L : FrequencyCutoff) (p : ℝ≥0), smoothingThreshold d ≤ p →
      ∀ ε : ℝ, 0 < ε →
      (∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
        eLpNorm (G.cutoffAverage χ (L.band k f)) p volume ≤
          C * dyadicWeight (-((d+1 : ℕ) : ℝ)/(p : ℝ)+ε) k * eLpNorm f p volume) ∧
      DyadicMaximalEstimate G χ L p ε := by
  obtain ⟨O,hO,hx,hjets⟩ := G.exists_smooth_jet_smoothing_neighborhood hG x hd
  refine ⟨O,hO,hx,?_⟩
  intro χ hχ hc hs L p hp ε hε
  have hB : BandSobolevInput G χ L p d 0 :=
    G.bandSobolevInput_aux χ hχ hc (fun _ _ => hG.contDiffAt) L p
      ((smoothingThreshold_one_le d).trans hp) 0 le_rfl
  refine ⟨theorem_2_1_of_jet_smoothing G χ L p 0 ε
    (hjets χ hχ hc hs L p hp 0 ε hε),?_⟩
  simpa only [add_zero] using corollary_2_2_of_inputs G χ L p d ε 0
    (hjets χ hχ hc hs L p hp d ε hε) hB

theorem Family.theorem_2_1_smooth_proved {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (x : ℝ × Parameters 2 d) (hd : G.cinematicDet x ≠ 0) :
    ∃ O : Set (ℝ × Parameters 2 d), IsOpen O ∧ x ∈ O ∧
      ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∀ (L : FrequencyCutoff) (p : ℝ≥0), smoothingThreshold d ≤ p →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
        Integrable f → MemLp f p volume →
        eLpNorm (G.cutoffAverage χ (L.band k f)) p volume ≤
          C * dyadicWeight (-((d+1 : ℕ) : ℝ)/(p : ℝ)+ε) k * eLpNorm f p volume := by
  obtain ⟨O,hO,hx,h⟩ := G.exists_smooth_local_smoothing hG x hd
  exact ⟨O,hO,hx,fun χ hχ hc hs L p hp ε hε => (h χ hχ hc hs L p hp ε hε).1⟩

theorem Family.corollary_2_2_smooth_proved {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (x : ℝ × Parameters 2 d) (hd : G.cinematicDet x ≠ 0) :
    ∃ O : Set (ℝ × Parameters 2 d), IsOpen O ∧ x ∈ O ∧
      ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∀ (L : FrequencyCutoff) (p : ℝ≥0), smoothingThreshold d ≤ p →
      ∀ ε : ℝ, 0 < ε → DyadicMaximalEstimate G χ L p ε := by
  obtain ⟨O,hO,hx,h⟩ := G.exists_smooth_local_smoothing hG x hd
  exact ⟨O,hO,hx,fun χ hχ hc hs L p hp ε hε => (h χ hχ hc hs L p hp ε hε).2⟩

end PlanarNikodym
