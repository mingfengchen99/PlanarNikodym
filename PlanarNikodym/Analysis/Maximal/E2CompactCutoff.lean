import PlanarNikodym.Analysis.Maximal.E3SmoothMaximalExclusion

/-! One actual compact cutoff covers the whole product of the original
closed time interval and any compact parameter set. Thus local cutoff
estimates require no countably varying constants at the final assembly. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlanarNikodym

theorem Family.exists_compact_interval_cutoff_e2 {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (K : Set (Parameters 2 d)) (hK : IsCompact K)
    (hd : ∀ t ∈ G.I.carrier, ∀ q ∈ K, G.cinematicDet (t, q) ≠ 0) :
    ∃ χ : Cutoff d, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ t ∈ G.I.carrier, ∀ q ∈ K, χ (t, q) = 1) ∧
      (∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) := by
  let S : Set (ℝ × Parameters 2 d) := {x | G.cinematicDet x ≠ 0}
  have hS : IsOpen S := (G.continuous_cinematicDet_of_contDiff hG).isOpen_preimage _
    isClosed_singleton.isOpen_compl
  obtain ⟨χ, N, hχ, hc, hr, _hN, hKN, hN1, hχS⟩ :=
    exists_compact_smooth_cutoff (isCompact_Icc.prod hK) hS
      (by rintro ⟨t, q⟩ ⟨ht, hq⟩; exact hd t ht q hq)
  exact ⟨χ, hχ, hc, hr, fun t ht q hq => hN1 (t, q) (hKN ⟨ht, hq⟩), hχS⟩

end PlanarNikodym
