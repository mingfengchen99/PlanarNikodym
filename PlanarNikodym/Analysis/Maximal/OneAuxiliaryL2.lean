import PlanarNikodym.Analysis.Jets.CinematicScalarL2
import PlanarNikodym.Analysis.Jets.ScalarJetSmoothing
import PlanarNikodym.Analysis.Sobolev.GeneralBandSobolev

/-! The genuine one-auxiliary-parameter L2 endpoint for the original
frequency-band maximal operator. The full normalized jet gain is proved
first, and the auxiliary Sobolev factor cancels its half derivative. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

theorem Family.one_auxiliary_jet_L2_proved (G : Family 2 1)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2))
    (χ : Cutoff 1) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (s : ℕ) : JetSmoothingInput G χ L 2 s (1/2) := by
  apply G.jetSmoothingInput_of_scalarJet_estimates χ hχ hc
    (fun _ _ => hG.contDiffAt) L 2 (by norm_num) s (1/2)
  intro ψ hψ hcψ hsψ m
  obtain ⟨C,hC⟩ := G.exists_cinematic_scalar_weighted_dyadic_L2 hG ψ hψ hcψ
    (fun x hx => hd x (hsψ hx)) L m
  refine ⟨C,?_⟩
  intro k f hf hf2
  convert hC k f hf hf2 using 1 <;> norm_num

theorem Family.one_auxiliary_band_maximal_L2_proved (G : Family 2 1)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2))
    (χ : Cutoff 1) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) :
    ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f 2 volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) 2 volume ≤ C * eLpNorm f 2 volume := by
  have hB := G.bandSobolevInput_aux χ hχ hc (fun _ _ => hG.contDiffAt) L 2
    (by norm_num) 0 (le_refl 0)
  have h := corollary_2_2_of_inputs G χ L 2 1 (1/2) 0
    (G.one_auxiliary_jet_L2_proved hG χ hχ hc hd L 1) hB
  obtain ⟨C,hC⟩ := h
  refine ⟨C,?_⟩
  intro k f hf hf2
  have hh := hC k f hf hf2
  norm_num [dyadicWeight] at hh
  exact hh

end PlanarNikodym
