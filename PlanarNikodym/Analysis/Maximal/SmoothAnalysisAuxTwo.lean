import PlanarNikodym.Analysis.Sobolev.BandSobolevTwoRegularity
import PlanarNikodym.Analysis.Maximal.SmoothAnalysisClassification
import PlanarNikodym.Analysis.Localization.AnalyticCutoff

/-! The actual two-dimensional Sobolev proof supplies the Sobolev field of
the smooth maximal package. Only jet smoothing remains an analytic estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal

namespace PlanarNikodym

/-- For two auxiliary parameters the package's Sobolev estimate follows
from actual `C²` geometry; the remaining estimate is jet smoothing. -/
def smoothMaximalPackage_aux_two (G : Family 2 2) (U : Set (Parameters 2 2))
    (χ : Cutoff 2) (L : FrequencyCutoff) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 2 (fun x : ℝ × Parameters 2 2 => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ q ∈ U, 1 ≤ χ (t, q))
    (p : ℝ≥0) (hp : smoothingThreshold 2 ≤ p)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / (p : ℝ))
    (hS : JetSmoothingInput G χ L p 2 ε) : SmoothMaximalPackage G U := by
  have hp1 : 1 ≤ p :=
    (by norm_num [smoothingThreshold] : (1 : ℝ≥0) ≤ smoothingThreshold 2).trans hp
  let δ : ℝ := (1 / (p : ℝ) - ε) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  exact {
    frequency := L
    cutoff := χ
    cutoff_smooth := hχ
    cutoff_compact := hc
    gamma_regular_at_support := fun x hx => (hγ x hx).of_le (by norm_num)
    cutoff_nonnegative := hχ0
    cutoff_one := hχ1
    p := p
    p_ge_one := hp1
    p_ge_threshold := hp
    jetOrder := 2
    jetOrder_gt := by
      have hd := smoothingThreshold_sobolev_order_one 2 p hp
      change (2 : ℝ) / (p : ℝ) < 2
      exact hd.trans (by norm_num)
    smoothingLoss := ε
    sobolevLoss := δ
    smoothingLoss_pos := hε0
    sobolevLoss_pos := hδ
    loss_lt := by dsimp [δ]; linarith
    smoothing := hS
    sobolev := G.bandSobolevInput_aux_two χ (contDiff_infty.mp hχ 2) hc hγ L p hp1 δ hδ.le }

/-- In two auxiliary dimensions, the actual jet-smoothing estimate alone,
with ordinary cutoff and geometric hypotheses, gives the open-set estimate. -/
theorem Family.openMaximalEstimate_aux_two_of_jet_smoothing (G : Family 2 2)
    (U : Set (Parameters 2 2)) (hU : IsOpen U) (hUW : U ⊆ G.W) (hs : G.IsSmooth)
    (χ : Cutoff 2) (L : FrequencyCutoff) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 2 (fun x : ℝ × Parameters 2 2 => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ q ∈ U, 1 ≤ χ (t, q))
    (p : ℝ≥0) (hp : smoothingThreshold 2 ≤ p)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / (p : ℝ))
    (hS : JetSmoothingInput G χ L p 2 ε) : G.OpenMaximalEstimate U :=
  (smoothMaximalPackage_aux_two G U χ L hχ hc hγ hχ0 hχ1 p hp ε hε0 hε hS).open_maximal_estimate
    hU hUW hs

/-- Actual analytic cinematic geometry supplies a smooth cutoff on the
whole closed interval, with a proved two-dimensional Sobolev input for
every frequency cutoff, finite `p ≥ 1`, and nonnegative loss. -/
theorem Family.exists_cinematic_sobolev_cutoff_aux_two (G : Family 2 2)
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (hn : ∀ t ∈ G.I.carrier, ∀ q ∈ G.W, G.cinematicDet (t, q) ≠ 0)
    (q : Parameters 2 2) (hq : q ∈ G.W) :
    ∃ (U : Set (Parameters 2 2)) (χ : Cutoff 2),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ t ∈ G.I.carrier, ∀ r ∈ U, χ (t, r) = 1) ∧
      (∀ x ∈ tsupport χ, AnalyticAt ℝ (fun x : ℝ × Parameters 2 2 => G.γ x.1 x.2) x ∧
        G.cinematicDet x ≠ 0) ∧
      (∀ (L : FrequencyCutoff) (p : ℝ≥0), 1 ≤ p → ∀ δ : ℝ, 0 ≤ δ →
        BandSobolevInput G χ L p 2 δ) := by
  obtain ⟨U, χ, hU, hqU, hUW, hχ, hc, hr, hχ1, hγ⟩ :=
    G.exists_cinematic_cutoff_neighborhood ho ha hn q hq
  refine ⟨U, χ, hU, hqU, hUW, hχ, hc, hr, hχ1, hγ, ?_⟩
  intro L p hp δ hδ
  exact G.bandSobolevInput_aux_two χ (contDiff_infty.mp hχ 2) hc
    (fun x hx => (hγ x hx).1.contDiffAt) L p hp δ hδ

end PlanarNikodym
