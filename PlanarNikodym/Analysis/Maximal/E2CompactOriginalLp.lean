import PlanarNikodym.Analysis.Maximal.E2CompactParameterAssembly
import PlanarNikodym.Analysis.Maximal.E2IntervalLpExtension

/-! The full original compact-domain maximal operator, including its
ambient Lᵖ extension. Only the explicitly stated geometric endpoint is
conditional; the compact cutoff, original closed interval, finite-valued
supremum, measurability, frequency sum and extension are proved. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem Family.compact_intervalMaximal_e2_Lp_of_geometric_endpoint {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t, q) ≠ 0)
    (L : FrequencyCutoff)
    (hgeometric : ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x) → (∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (hp : (d + 2 : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f := by
  obtain ⟨C, hC⟩ := G.compact_intervalMaximal_e2_bound_of_geometric_endpoint hG hdim
    K hK hKW hd L hgeometric p hp
  refine ⟨C, ?_⟩
  exact G.exists_intervalMaximal_Lp_extension_e2 hG.contDiffOn K hK hKW p ENNReal.coe_ne_top C
    (fun f hf hfc hfp => (hC f hf hfc hfp).2)

end PlanarNikodym
