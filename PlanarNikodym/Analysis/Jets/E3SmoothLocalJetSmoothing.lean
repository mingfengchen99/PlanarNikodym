import PlanarNikodym.Analysis.Jets.E3SmoothJetSmoothing
import PlanarNikodym.Analysis.Fourier.GlyzLocalPhaseTransport

/-! The actual finite-jet estimate for a phase smooth only on an open
neighborhood of the compact cutoff support. A genuine smooth extension
preserves the entire cutoff average, hence all actual auxiliary jets. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal NNReal Topology
namespace PlanarNikodym

theorem Family.e3_cutoffAverage_eq_of_eqOn_support {d : ℕ}
    (G H : Family 2 d) (χ : Cutoff d)
    (heq : ∀ x ∈ tsupport χ, G.γ x.1 x.2 = H.γ x.1 x.2) (f : Plane → ℂ) :
    G.cutoffAverage χ f = H.cutoffAverage χ f := by
  funext q
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hz : χ (t, q) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · have h := heq (t, q) (subset_tsupport χ hz)
    simp only [Family.graphMap, h]

theorem Family.e3_scaledJetNorm_eq_of_cutoffAverage_eq {d : ℕ}
    (G H : Family 2 d) (χ : Cutoff d)
    (heq : ∀ f : Plane → ℂ, G.cutoffAverage χ f = H.cutoffAverage χ f)
    (f : Plane → ℂ) (p : ℝ≥0) (s k : ℕ) :
    G.scaledJetNorm χ f p s k = H.scaledJetNorm χ f p s k := by
  unfold Family.scaledJetNorm Family.auxiliaryJetNorm
  rw [heq f]

/-- Positive-dimensional Theorem 2.1 with all finite normalized jets,
requiring genuine C∞ regularity only on the declared open neighborhood. -/
theorem Family.e3_jetSmoothingInput_of_smooth_on_open {d : ℕ}
    (G : Family 2 d) (hdim : 1 ≤ d)
    {O : Set (ℝ × Parameters 2 d)} (hO : IsOpen O)
    (hG : ∀ x ∈ O, ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ O) (hχ0 : ∀ x, 0 ≤ χ x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    (s : ℕ) {ε : ℝ} (hε : 0 < ε) : JetSmoothingInput G χ L p s ε := by
  obtain ⟨Ψ, N, hΨ, _, hN, hKN, _, heq⟩ := exists_compact_smooth_extension
    (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) hc.isCompact hO hs hG
  let H : Family 2 d := {G with γ := fun t q => Ψ (t, q)}
  have hdet : ∀ x ∈ tsupport χ, H.cinematicDet x ≠ 0 := by
    intro x hx
    have he := H.cinematicDet_eq_of_eventuallyEq G (x := x) (by
      filter_upwards [hN.mem_nhds (hKN hx)] with y hy
      exact heq hy)
    rw [he]
    exact hd x hx
  have havg : ∀ f : Plane → ℂ, H.cutoffAverage χ f = G.cutoffAverage χ f :=
    fun f => H.e3_cutoffAverage_eq_of_eqOn_support G χ (fun _ hx => heq (hKN hx)) f
  obtain ⟨C, hC⟩ := H.e3_jetSmoothingInput_of_cinematic_support hΨ hdim χ hχ hc hχ0 hdet
    L p hp s hε
  refine ⟨C, fun k f hf hfp => ?_⟩
  rw [← H.e3_scaledJetNorm_eq_of_cutoffAverage_eq G χ havg (L.band k f) p s k]
  exact hC k f hf hfp

end PlanarNikodym
