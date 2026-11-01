import PlanarNikodym.Analysis.Maximal.E2CompactOriginalLp

/-! Original compact-domain operator transport from an explicitly declared
open smooth neighborhood of I × K. The new globally smooth phase is
constructed, and preserves the original entire closed-interval operator. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ContDiff Topology
namespace PlanarNikodym

theorem Family.exists_compact_original_smooth_extension_e2 {d : ℕ} (G : Family 2 d)
    (K : Set (Parameters 2 d)) (hK : IsCompact K)
    {O : Set (ℝ × Parameters 2 d)} (hO : IsOpen O) (hKO : G.I.carrier ×ˢ K ⊆ O)
    (hG : ∀ x ∈ O, ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t, q) ≠ 0) :
    ∃ H : Family 2 d, H.I = G.I ∧ H.W = G.W ∧
      ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => H.γ x.1 x.2) ∧
      (∀ t ∈ H.I.carrier, ∀ q ∈ K, H.cinematicDet (t, q) ≠ 0) ∧
      ∀ f : Plane → ℂ, H.intervalMaximal_e2 K f = G.intervalMaximal_e2 K f := by
  obtain ⟨Ψ, N, hΨ, _, hN, hKN, _, heq⟩ := exists_compact_smooth_extension
    (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) (isCompact_Icc.prod hK) hO hKO hG
  let H : Family 2 d := {G with γ := fun t q => Ψ (t, q)}
  refine ⟨H, rfl, rfl, hΨ, ?_, ?_⟩
  · intro t ht q hq
    have he := H.cinematicDet_eq_of_eventuallyEq G (x := (t, q)) (by
      filter_upwards [hN.mem_nhds (hKN ⟨ht, hq⟩)] with y hy
      exact heq hy)
    rw [he]
    exact hd t ht q hq
  · intro f
    funext z
    unfold intervalMaximal_e2
    apply iSup_congr
    intro u
    apply iSup_congr
    intro hu
    have he : H.intervalAverage_e2 f (z, u) = G.intervalAverage_e2 f (z, u) := by
      unfold intervalAverage_e2
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have hh := heq (hKN (show (t, (z, u)) ∈ G.I.carrier ×ˢ K from ⟨ht, hu⟩))
      simp only [Family.graphMap, H]
      rw [hh]
    rw [he]

theorem Family.compact_intervalMaximal_e2_Lp_of_geometric_on_open {d : ℕ} (G : Family 2 d)
    (hdim : 1 ≤ d) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    {O : Set (ℝ × Parameters 2 d)} (hO : IsOpen O) (hKO : G.I.carrier ×ˢ K ⊆ O)
    (hG : ∀ x ∈ O, ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t, q) ≠ 0) (L : FrequencyCutoff)
    (hgeometric : ∀ H : Family 2 d,
      ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => H.γ x.1 x.2) →
      ∀ χ : Cutoff d, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ x, 0 ≤ χ x) → (∀ x ∈ tsupport χ, H.cinematicDet x ≠ 0) →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ,
      Integrable f → MemLp f (d + 2 : ℝ≥0) volume →
      eLpNorm (H.cutoffMaximal χ (L.band k f)) (d + 2 : ℝ≥0) volume ≤
        C * dyadicWeight ε k * eLpNorm f (d + 2 : ℝ≥0) volume)
    (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] (hp : (d + 2 : ℝ≥0) < p) :
    ∃ C : ℝ≥0, ∃ T : Lp ℂ p (volume : Measure Plane) → Lp ℂ p (volume : Measure (Base 2)),
      LipschitzWith C T ∧ T 0 = 0 ∧ (∀ u, ‖T u‖ ≤ C * ‖u‖) ∧
      ∀ (f : Plane → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (hfp : MemLp f p volume),
        (T (hfp.toLp f) : Base 2 → ℂ) =ᵐ[volume] G.intervalMaximalComplex_e2 K f := by
  obtain ⟨H, _hHI, hHW, hH, hHd, hmax⟩ :=
    G.exists_compact_original_smooth_extension_e2 K hK hO hKO hG hd
  have hKH : K ⊆ H.W := by rwa [hHW]
  obtain ⟨C, T, hLip, hzero, hbound, hagree⟩ :=
    H.compact_intervalMaximal_e2_Lp_of_geometric_endpoint hH hdim K hK hKH hHd L
      (hgeometric H hH) p hp
  refine ⟨C, T, hLip, hzero, hbound, ?_⟩
  intro f hf hfc hfp
  have he : H.intervalMaximalComplex_e2 K f = G.intervalMaximalComplex_e2 K f := by
    funext z
    unfold intervalMaximalComplex_e2
    rw [hmax f]
  rw [← he]
  exact hagree f hf hfc hfp

end PlanarNikodym
