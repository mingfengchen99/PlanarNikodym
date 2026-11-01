import PlanarNikodym.Analysis.Fourier.NonstationaryRegion

/-! An actual smooth main/error frequency split. The error support lies
in a uniformly nonstationary region of the true graph phase. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace PlanarNikodym

/-- A smooth vertical-frequency cutoff chosen from the actual compact
time-slope bound. Both frequency symbols are compactly supported, and
the error phase has a fixed positive lower bound for its time derivative. -/
theorem Family.exists_microlocal_band_split {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) :
    ∃ (δ : ℝ) (β : ℝ → ℝ), 0 < δ ∧ δ ≤ 1 / 4 ∧ ContDiff ℝ ∞ β ∧
      (∀ s, 0 ≤ β s ∧ β s ≤ 1) ∧
      (∀ s, |s| ≤ δ / 2 → β s = 0) ∧ (∀ s, δ ≤ |s| → β s = 1) ∧
      HasCompactSupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ∧
      HasCompactSupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)) ∧
      (∀ ξ : Plane, L.bandSymbol 0 ξ = L.bandSymbol 0 ξ * β ξ.2 +
        L.bandSymbol 0 ξ * (1 - β ξ.2)) ∧
      ∀ ξ ∈ tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * (1 - β ξ.2)),
        ∀ x ∈ tsupport χ, 1 / 2 ≤ |deriv (G.graphPhase x.2 ξ) x.1| := by
  obtain ⟨δ, hδ, hδle, hnonstat⟩ := G.exists_uniform_nonstationary_region χ hc hγ
  let b : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let β : ℝ → ℝ := fun s => 1 - b s
  refine ⟨δ, β, hδ, hδle, contDiff_const.sub b.contDiff, ?_, ?_, ?_,
    (L.bandSymbol_compact 0).mul_right, (L.bandSymbol_compact 0).mul_right, ?_, ?_⟩
  · intro s
    have h₀ := b.nonneg' s
    have h₁ := b.le_one (x := s)
    dsimp [β]
    constructor <;> linarith
  · intro s hs
    have hb : b s = 1 := b.one_of_mem_closedBall (by simpa [b, mem_closedBall_zero_iff, Real.norm_eq_abs] using hs)
    simp only [β, hb, sub_self]
  · intro s hs
    have hb : b s = 0 := b.zero_of_le_dist (by simpa [b, Real.dist_eq] using hs)
    simp only [β, hb, sub_zero]
  · intro ξ
    ring
  · intro ξ hξ x hx
    have heq : (fun η : Plane => L.bandSymbol 0 η * (1 - β η.2)) =
        fun η => L.bandSymbol 0 η * b η.2 := by funext η; dsimp [β]; ring
    rw [heq] at hξ
    have hnorm : 1 ≤ ‖ξ‖ := by
      simpa only [pow_zero] using L.bandSymbol_tsupport_norm_ge_scale 0
        (tsupport_mul_subset_left hξ)
    have hb : ξ.2 ∈ tsupport (b : ℝ → ℝ) :=
      tsupport_comp_subset_preimage (b : ℝ → ℝ) continuous_snd (tsupport_mul_subset_right hξ)
    have hsmall : |ξ.2| ≤ δ := by
      simpa only [b.tsupport_eq, mem_closedBall_zero_iff, Real.norm_eq_abs, b] using hb
    exact hnonstat x hx ξ hnorm hsmall

end PlanarNikodym
