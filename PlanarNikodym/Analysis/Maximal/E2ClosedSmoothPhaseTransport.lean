import PlanarNikodym.Analysis.Maximal.E2WithinCinematic
import PlanarNikodym.Analysis.Maximal.E2CompactPhaseTransport

/-! The original closed interval operator, transported through the
constructed Seeley extension. Closed-domain cinematic hypotheses use
intrinsic within jets; genuine ambient C^(d+2) recovers the old matrix. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal ContDiff Topology Matrix
namespace PlanarNikodym

theorem Family.exists_compact_closed_smooth_extension_e2 {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hG : G.IsSmooth)
    (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W) :
    ∃ H : Family 2 d, H.I = G.I ∧ H.W = G.W ∧
      ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => H.γ x.1 x.2) ∧
      (∀ x ∈ G.I.carrier ×ˢ K, H.cinematicMatrix x = G.cinematicMatrixWithin_e2 x) ∧
      ∀ f : Plane → ℂ, H.intervalMaximal_e2 K f = G.intervalMaximal_e2 K f := by
  obtain ⟨Ψ, hΨ, heq, hj⟩ := e2_exists_contDiff_extension_closed_product_with_jets
    G.I.nondegenerate hW hK hKW hG
  let H : Family 2 d := {G with γ := fun t q => Ψ (t, q)}
  refine ⟨H, rfl, rfl, hΨ, ?_, ?_⟩
  · intro x hx
    ext i j
    have hreg : ContDiffAt ℝ (i.val + 1) Ψ x := hΨ.contDiffAt.of_le (by
      exact_mod_cast (show (i.val + 1 : ℕ∞) ≤ ⊤ from le_top))
    change timeDerivative (fun y => fderiv ℝ Ψ y
      (0, parameterFrame d (Pi.single j 1))) i.val x = _
    rw [e2_timeParameterDerivative_eq_fullJet i.val hreg, hj x hx (i.val + 1)]
    rfl
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
      have hh := heq (show (t, (z, u)) ∈ G.I.carrier ×ˢ K from ⟨ht, hu⟩)
      simp only [Family.graphMap, H]
      rw [hh]
    rw [he]

theorem Family.compact_intervalMaximal_e2_Lp_of_closed_smooth_within_cinematic
    {d : ℕ} (G : Family 2 d) (hW : IsOpen G.W) (hG : G.IsSmooth)
    (hdim : 1 ≤ d) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDetWithin_e2 (t, q) ≠ 0)
    (L : FrequencyCutoff)
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
  obtain ⟨H, hI, hHW, hH, hjet, hmax⟩ :=
    G.exists_compact_closed_smooth_extension_e2 hW hG K hK hKW
  have hKH : K ⊆ H.W := by rwa [hHW]
  have hHd : ∀ t ∈ H.I.carrier, ∀ q ∈ K, H.cinematicDet (t, q) ≠ 0 := by
    intro t ht q hq
    have htG : t ∈ G.I.carrier := by rwa [hI] at ht
    unfold cinematicDet
    rw [hjet (t, q) ⟨htG, hq⟩]
    exact hd t htG q hq
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

theorem Family.compact_intervalMaximal_e2_Lp_of_closed_smooth_ambient_jets
    {d : ℕ} (G : Family 2 d) (hW : IsOpen G.W) (hG : G.IsSmooth)
    (hdim : 1 ≤ d) (K : Set (Parameters 2 d)) (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hGreg : ∀ x ∈ G.I.carrier ×ˢ K, ContDiffAt ℝ (d + 2)
      (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t, q) ≠ 0)
    (L : FrequencyCutoff)
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
  apply G.compact_intervalMaximal_e2_Lp_of_closed_smooth_within_cinematic
    hW hG hdim K hK hKW _ L hgeometric p hp
  intro t ht q hq
  rw [G.cinematicDetWithin_e2_eq_ambient hW ⟨ht, hKW hq⟩ (hGreg (t, q) ⟨ht, hq⟩)]
  exact hd t ht q hq

end PlanarNikodym
