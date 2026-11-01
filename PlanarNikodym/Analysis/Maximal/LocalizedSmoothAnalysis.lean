import PlanarNikodym.Analysis.Localization.JetLocalization
import PlanarNikodym.Avoidance.ProvedAvoidance

/-! Pointwise small-support jet estimates imply the existing cinematic
analysis interface. The actual cutoff, finite partition, Sobolev estimate
and loss budget are constructed here. The pointwise estimate is supplied
by the downstream theorem `pointwise_jet_smoothing_input`. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal

namespace PlanarNikodym

/-- The pointwise local jet-smoothing interface. Each estimate is for all
inputs and frequencies with a fixed cutoff-dependent constant.
`pointwise_jet_smoothing_input` constructs this proposition without
additional analytic premises. -/
def PointwiseJetSmoothingInput : Prop :=
  ∀ (d : ℕ) (G : Family 2 d) (L : FrequencyCutoff) (p : ℝ≥0),
    smoothingThreshold d ≤ p → ∀ s : ℕ, d ≤ s → 0 < s → ∀ ε : ℝ, 0 < ε →
    ∀ x : ℝ × Parameters 2 d,
      AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x →
      G.cinematicDet x ≠ 0 → ∃ O : Set (ℝ × Parameters 2 d),
        IsOpen O ∧ x ∈ O ∧ ∀ ψ : Cutoff d,
          ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
            JetSmoothingInput G ψ L p s ε

/-- The entire finite time/parameter localization and loss-budget step is
proved from the pointwise small-support analytic estimate. -/
theorem cinematicSmoothAnalysisInput_of_pointwise_jet_smoothing
    (H : PointwiseJetSmoothingInput) : CinematicSmoothAnalysisInput := by
  intro d G ho ha hn q hq
  obtain ⟨U, χ, hU, hqU, hUW, hχ, hc, hr, hχ1, hγ⟩ :=
    G.exists_cinematic_cutoff_neighborhood ho ha hn q hq
  let L := standardFrequencyCutoff
  let p := smoothingThreshold d
  let ε : ℝ := 1 / (4 * (p : ℝ))
  have hp1 : (1 : ℝ≥0) ≤ p := by
    dsimp [p, smoothingThreshold]
    nlinarith [show (0 : ℝ≥0) ≤ d from zero_le]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp1)
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε : ε < 1 / (p : ℝ) := by
    dsimp [ε]
    exact one_div_lt_one_div_of_lt hpR (by nlinarith)
  have hregular : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x :=
    fun x hx => (hγ x hx).1.contDiffAt
  have hS : JetSmoothingInput G χ L p (d + 1) ε := by
    apply jetSmoothingInput_of_local_cutoffs G χ hχ hc (fun x => (hr x).1)
      hregular L p hp1 (d + 1) ε
    intro x hx
    exact H d G L p le_rfl (d + 1) (Nat.le_succ d) (Nat.succ_pos d) ε hε0 x
      (hγ x hx).1 (hγ x hx).2
  refine ⟨U, hU, hqU, hUW, ⟨?_⟩⟩
  exact smoothMaximalPackage_aux G U χ L hχ hc hregular (fun x => (hr x).1)
    (fun t ht r hr => (hχ1 t ht r hr).symm.le) p le_rfl ε hε0 hε
    (Nat.le_succ d) (Nat.succ_pos d) hS

theorem theorem_1_5_of_pointwise_jet_smoothing (H : PointwiseJetSmoothingInput)
    (hP : ProjectionConstructionInput) : Theorem15Statement :=
  theorem_1_5_after_avoidance (cinematicSmoothAnalysisInput_of_pointwise_jet_smoothing H) hP

theorem theorem_1_4_of_pointwise_jet_smoothing (H : PointwiseJetSmoothingInput)
    (hP : ProjectionConstructionInput) (hD : ConnectedCellInput) : Theorem14Statement :=
  theorem_1_4_after_avoidance (cinematicSmoothAnalysisInput_of_pointwise_jet_smoothing H) hP hD

theorem proposition_1_6_of_pointwise_jet_smoothing (H : PointwiseJetSmoothingInput)
    (hP : ProjectionConstructionInput) (hD : AnalyticCellInput) : Proposition16Statement :=
  proposition_1_6_after_avoidance (cinematicSmoothAnalysisInput_of_pointwise_jet_smoothing H) hP hD

end PlanarNikodym
