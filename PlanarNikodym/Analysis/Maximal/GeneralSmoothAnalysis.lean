import PlanarNikodym.Analysis.Sobolev.GeneralBandSobolev
import PlanarNikodym.Analysis.Maximal.SmoothAnalysisAuxTwo

/-! The proved general-dimensional Sobolev estimate fills the Sobolev field
of the actual smooth maximal package in every finite dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal

namespace PlanarNikodym

/-- A finite jet of order at least the auxiliary dimension supplies the
Sobolev estimate automatically. Jet smoothing remains the sole analytic
estimate passed to this constructor. -/
def smoothMaximalPackage_aux {d s : ℕ} (G : Family 2 d) (U : Set (Parameters 2 d))
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ q ∈ U, 1 ≤ χ (t, q))
    (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / (p : ℝ))
    (hds : d ≤ s) (hs : 0 < s) (hS : JetSmoothingInput G χ L p s ε) :
    SmoothMaximalPackage G U := by
  have hp1 : 1 ≤ p := by
    apply le_trans (b := smoothingThreshold d) _ hp
    dsimp [smoothingThreshold]
    nlinarith [show (0 : ℝ≥0) ≤ d from zero_le]
  let δ : ℝ := (1 / (p : ℝ) - ε) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  exact {
    frequency := L
    cutoff := χ
    cutoff_smooth := hχ
    cutoff_compact := hc
    gamma_regular_at_support := fun x hx => (hγ x hx).of_le (by simp)
    cutoff_nonnegative := hχ0
    cutoff_one := hχ1
    p := p
    p_ge_one := hp1
    p_ge_threshold := hp
    jetOrder := s
    jetOrder_gt := (smoothingThreshold_sobolev_order_one d p hp).trans_le
      (by exact_mod_cast hs)
    smoothingLoss := ε
    sobolevLoss := δ
    smoothingLoss_pos := hε0
    sobolevLoss_pos := hδ
    loss_lt := by dsimp [δ]; linarith
    smoothing := hS
    sobolev := G.bandSobolevInput_aux_of_order_ge χ hχ hc hγ L p hp1 δ hδ.le hds }

theorem Family.openMaximalEstimate_of_jet_smoothing {d s : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) (hU : IsOpen U) (hUW : U ⊆ G.W) (hsmooth : G.IsSmooth)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ q ∈ U, 1 ≤ χ (t, q))
    (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / (p : ℝ))
    (hds : d ≤ s) (hs : 0 < s) (hS : JetSmoothingInput G χ L p s ε) :
    G.OpenMaximalEstimate U :=
  (smoothMaximalPackage_aux G U χ L hχ hc hγ hχ0 hχ1 p hp ε hε0 hε hds hs hS).open_maximal_estimate
    hU hUW hsmooth

/-- Actual analytic cinematic geometry supplies the cutoff and every
general-dimensional Sobolev input used by the jet-smoothing route. -/
theorem Family.exists_cinematic_sobolev_cutoff {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (hn : ∀ t ∈ G.I.carrier, ∀ q ∈ G.W, G.cinematicDet (t, q) ≠ 0)
    (q : Parameters 2 d) (hq : q ∈ G.W) :
    ∃ (U : Set (Parameters 2 d)) (χ : Cutoff d),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ t ∈ G.I.carrier, ∀ r ∈ U, χ (t, r) = 1) ∧
      (∀ x ∈ tsupport χ, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x ∧
        G.cinematicDet x ≠ 0) ∧
      (∀ (L : FrequencyCutoff) (p : ℝ≥0), 1 ≤ p → ∀ δ : ℝ, 0 ≤ δ →
        ∀ s : ℕ, d ≤ s → BandSobolevInput G χ L p s δ) := by
  obtain ⟨U, χ, hU, hqU, hUW, hχ, hc, hr, hχ1, hγ⟩ :=
    G.exists_cinematic_cutoff_neighborhood ho ha hn q hq
  refine ⟨U, χ, hU, hqU, hUW, hχ, hc, hr, hχ1, hγ, ?_⟩
  intro L p hp δ hδ s hds
  exact G.bandSobolevInput_aux_of_order_ge χ hχ hc (fun x hx => (hγ x hx).1.contDiffAt)
    L p hp δ hδ hds

end PlanarNikodym
