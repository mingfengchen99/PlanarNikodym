import PlanarNikodym.Analysis.Jets.ScalarJetSmoothing
import PlanarNikodym.Analysis.Jets.ScalarWeightedSmoothing
import PlanarNikodym.Analysis.Maximal.LocalizedSmoothAnalysis

/-! Actual finite auxiliary-jet smoothing. The scalar weighted theorem
is applied to the finitely many differentiated amplitudes, so no analytic
estimate remains as a premise. The neighborhood is chosen before the
cutoff, the derivative order, the frequency and the input. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

/-- Every finite auxiliary-jet order has the actual normalized estimate
on one fixed regular neighborhood of the given point. -/
theorem Family.exists_jet_smoothing_neighborhood {d : ℕ}
    (G : Family 2 d) (x : ℝ × Parameters 2 d)
    (ha : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : G.cinematicDet x ≠ 0) :
    ∃ O : Set (ℝ × Parameters 2 d), IsOpen O ∧ x ∈ O ∧
      ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∀ (L : FrequencyCutoff) (p : ℝ≥0), smoothingThreshold d ≤ p →
      ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → JetSmoothingInput G χ L p s ε := by
  obtain ⟨O, hO, hx, hreg, hscalar⟩ :=
    G.exists_scalar_weighted_smoothing_neighborhood x ha hd
  refine ⟨O, hO, hx, ?_⟩
  intro χ hχ hc hs L p hp s ε hε
  apply G.jetSmoothingInput_of_scalarJet_estimates χ hχ hc
    (fun y hy => (hreg y (hs hy)).contDiffAt) L p
    ((smoothingThreshold_one_le d).trans hp) s ε
  intro ψ hψ hcψ hsψ m
  exact hscalar ψ hψ hcψ (hsψ.trans hs) L p hp ε hε m

/-- The pointwise jet-smoothing interface is now supplied by a proof. -/
theorem pointwise_jet_smoothing_input : PointwiseJetSmoothingInput := by
  intro d G L p hp s _ _ ε hε x ha hd
  obtain ⟨O, hO, hx, h⟩ := G.exists_jet_smoothing_neighborhood x ha hd
  exact ⟨O, hO, hx, fun χ hχ hc hs => h χ hχ hc hs L p hp s ε hε⟩

/-- Finite localization gives the full compact-cutoff jet estimate,
with a single constant independent of the dyadic frequency and input. -/
theorem Family.jetSmoothingInput_of_cinematic_support {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    (s : ℕ) {ε : ℝ} (hε : 0 < ε) : JetSmoothingInput G χ L p s ε := by
  apply jetSmoothingInput_of_local_cutoffs G χ hχ hc hχ0
    (fun x hx => (ha x hx).contDiffAt) L p
    ((smoothingThreshold_one_le d).trans hp) s ε
  intro x hx
  obtain ⟨O, hO, hxO, h⟩ := G.exists_jet_smoothing_neighborhood x (ha x hx) (hd x hx)
  exact ⟨O, hO, hxO, fun ψ hψ hcψ hsψ => h ψ hψ hcψ hsψ L p hp s ε hε⟩

/-- The actual scalar conclusion of Theorem 2.1 on compact cinematic
support; the jet estimate has been proved rather than assumed. -/
theorem Family.theorem_2_1_proved {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffAverage χ (L.band k f)) p volume ≤
        C * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k * eLpNorm f p volume :=
  theorem_2_1_of_jet_smoothing G χ L p 0 ε
    (G.jetSmoothingInput_of_cinematic_support χ hχ hc hχ0 ha hd L p hp 0 hε)

/-- The local maximal packages required for cinematic exclusion are
constructed from the proved pointwise auxiliary-jet estimate. -/
theorem cinematic_smooth_analysis_input : CinematicSmoothAnalysisInput :=
  cinematicSmoothAnalysisInput_of_pointwise_jet_smoothing pointwise_jet_smoothing_input

/-- Cinematic families have no positive-measure incidence centers for a
null planar set, with no remaining analytic estimate premise. -/
theorem cinematic_null_input : CinematicNullInput :=
  cinematicNullInput_of_smooth_analysis cinematic_smooth_analysis_input

end PlanarNikodym
