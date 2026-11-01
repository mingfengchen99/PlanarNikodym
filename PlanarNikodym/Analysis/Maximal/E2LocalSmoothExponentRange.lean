import PlanarNikodym.Analysis.Maximal.E2SmoothExponentRange
import PlanarNikodym.Analysis.Jets.E3SmoothLocalJetSmoothing

/-! The same frequency decay and genuine ambient Lᵖ extension for a phase
smooth only on an open neighborhood of the compact cutoff support. A
constructed smooth extension preserves the whole actual cutoff operator. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ContDiff Topology
namespace PlanarNikodym

theorem Family.cutoffMaximal_eq_of_cutoffAverage_eq_e2 {d : ℕ}
    (G H : Family 2 d) (χ : Cutoff d)
    (heq : ∀ f : Plane → ℂ, G.cutoffAverage χ f = H.cutoffAverage χ f)
    (f : Plane → ℂ) : G.cutoffMaximal χ f = H.cutoffMaximal χ f := by
  funext z
  unfold cutoffMaximal
  rw [heq f]

theorem Family.exists_smooth_maximal_extension_e2 {d : ℕ} (G : Family 2 d)
    {O : Set (ℝ × Parameters 2 d)} (hO : IsOpen O)
    (hG : ∀ x ∈ O, ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (χ : Cutoff d) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) :
    ∃ H : Family 2 d,
      ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => H.γ x.1 x.2) ∧
      (∀ x ∈ tsupport χ, H.cinematicDet x ≠ 0) ∧
      ∀ f : Plane → ℂ, H.cutoffMaximal χ f = G.cutoffMaximal χ f := by
  obtain ⟨Ψ, N, hΨ, _, hN, hKN, _, heq⟩ := exists_compact_smooth_extension
    (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) hc.isCompact hO hs hG
  let H : Family 2 d := {G with γ := fun t q => Ψ (t, q)}
  refine ⟨H, hΨ, ?_, ?_⟩
  · intro x hx
    have he := H.cinematicDet_eq_of_eventuallyEq G (x := x) (by
      filter_upwards [hN.mem_nhds (hKN hx)] with y hy
      exact heq hy)
    rw [he]
    exact hd x hx
  · intro f
    exact H.cutoffMaximal_eq_of_cutoffAverage_eq_e2 G χ
      (fun f => H.e3_cutoffAverage_eq_of_eqOn_support G χ (fun _ hx => heq (hKN hx)) f) f

theorem Family.local_smooth_summable_dyadic_estimate_of_geometric_endpoint_e2 {d : ℕ}
    (G : Family 2 d) (hdim : 1 ≤ d)
    {O : Set (ℝ × Parameters 2 d)} (hO : IsOpen O)
    (hG : ∀ x ∈ O, ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ O) (hχ0 : ∀ x, 0 ≤ χ x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) (L : FrequencyCutoff)
    (hgeometric : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) (hp : (d + 2 : ℝ≥0) < p) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) p volume ≤
        C * dyadicWeight (-η) k * eLpNorm f p volume := by
  obtain ⟨H, hH, hHd, hmax⟩ := G.exists_smooth_maximal_extension_e2 hO hG χ hc hs hd
  have hgeoH : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (H.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume := by
    intro ε hε
    obtain ⟨C, hC⟩ := hgeometric ε hε
    refine ⟨C, fun k f hf hfp => ?_⟩
    rw [hmax]
    exact hC k f hf hfp
  obtain ⟨η, hη, C, hC⟩ := H.smooth_summable_dyadic_estimate_of_geometric_endpoint_e2
    hH hdim χ hχ hc hχ0 hHd L hgeoH p hp
  refine ⟨η, hη, C, fun k f hf hfp => ?_⟩
  rw [← hmax]
  exact hC k f hf hfp

theorem Family.local_smooth_Lp_extension_of_geometric_endpoint_e2 {d : ℕ} (G : Family 2 d)
    (hdim : 1 ≤ d) {O : Set (ℝ × Parameters 2 d)} (hO : IsOpen O)
    (hG : ∀ x ∈ O, ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ O) (hχ0 : ∀ x, 0 ≤ χ x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) (L : FrequencyCutoff)
    (hgeometric : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (hp : (d + 2 : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.cutoffMaximalComplex_e2 χ f := by
  obtain ⟨η, hη, CH, hCH⟩ := G.local_smooth_summable_dyadic_estimate_of_geometric_endpoint_e2
    hdim hO hG χ hχ hc hs hχ0 hd L hgeometric p hp
  have hp1 : 1 ≤ p := by linarith [NNReal.coe_nonneg (d : ℝ≥0)]
  obtain ⟨C, hC⟩ := G.cutoffMaximal_continuous_tests_of_summable_dyadic_e2 χ hχ.continuous hc
    (fun x hx => (hG x (hs hx)).continuousAt) L p hp1 hη CH hCH
  refine ⟨C, ?_⟩
  apply G.exists_cutoffMaximal_Lp_extension_e2 χ hχ.continuous hc
    (fun x hx => (hG x (hs hx)).continuousAt) p ENNReal.coe_ne_top C
  intro f hf hfc hfp
  obtain ⟨x₀, hx₀⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hfc.norm
  exact (hC f hf (hf.integrable_of_hasCompactSupport hfc) hfp ⟨‖f x₀‖, hx₀⟩).2

end PlanarNikodym
