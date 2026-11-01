import PlanarNikodym.Analysis.Fourier.RadialSymbolSplit

/-! Compact radial support for the smooth positive/negative pieces.
The upper bound is selected before scales and physical inputs. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym

theorem FrequencyCutoff.exists_positive_radial_support (L : FrequencyCutoff)
    (β : ℝ → ℝ) {κ : ℝ} (hz : ∀ η : ℝ, η < κ → β η = 0) :
    ∃ M : ℝ, Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ⊆ Icc κ M := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  obtain ⟨M, _, hM⟩ := (hc.isCompact.image continuous_snd).isBounded.exists_pos_norm_le
  have hs : tsupport m ⊆ Prod.snd ⁻¹' Ici κ := by
    apply closure_minimal _ (isClosed_Ici.preimage continuous_snd)
    intro ξ hξ
    change κ ≤ ξ.2
    by_contra h
    exact hξ (by dsimp [m]; rw [hz ξ.2 (lt_of_not_ge h), mul_zero])
  refine ⟨M, ?_⟩
  rintro η ⟨ξ, hξ, rfl⟩
  exact ⟨hs hξ, (le_abs_self ξ.2).trans (hM _ ⟨ξ, hξ, rfl⟩)⟩

end PlanarNikodym
