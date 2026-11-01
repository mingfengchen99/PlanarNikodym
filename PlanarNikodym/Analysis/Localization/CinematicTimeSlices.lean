import PlanarNikodym.Geometry.CinematicLowerMinors
import PlanarNikodym.Analysis.Localization.RegularTimeNeighborhood

/-! Finite localization of an actual cinematic cutoff with one common
time-scale threshold. Each local piece has selected original parameter
directions, a regular compact enlargement, and a positive minor bound
throughout every time segment of its sufficiently small time pieces. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace PlanarNikodym

theorem exists_common_time_scale_bound {ι : Type*} [Fintype ι]
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ ε i := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image ε)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, ?_⟩
  · have hmem := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]
      exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      rw [← hi]
      exact hε i
  · intro i
    exact Finset.min'_le S (ε i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))

theorem Family.isOpen_cinematicInitialMinor_regular {d m : ℕ} (G : Family 2 d)
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2)) (b : ℝ) :
    IsOpen {x : ℝ × Parameters 2 d |
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x ∧
        b < |G.cinematicInitialMinor hm σ x|} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact hx.1.eventually_analyticAt.and
    ((G.cinematicInitialMinor_analyticAt hm σ hx.1).continuousAt.abs.preimage_mem_nhds
      (Ioi_mem_nhds hx.2))

/-- This constructor starts from the real cinematic condition on the
original compact support. No minor selection, regular compact set, or
positive scale threshold is an additional input. -/
theorem Family.exists_finite_cinematic_regular_time_partition
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0) (m : ℕ) (hm : m ≤ d + 2) :
    ∃ (S : Finset (tsupport χ)) (ψ : S → Cutoff d)
      (σ : S → (Fin m ↪ Fin (d + 2))) (b : S → ℝ)
      (L : S → Set (ℝ × Parameters 2 d)) (ε : ℝ), 0 < ε ∧
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
        tsupport (ψ i) ⊆ tsupport χ ∧ (∀ x, 0 ≤ ψ i x ∧ ψ i x ≤ χ x) ∧
        IsCompact (L i) ∧ tsupport (ψ i) ⊆ L i ∧ 0 < b i ∧
        (∀ x ∈ L i, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x ∧
          b i ≤ |G.cinematicInitialMinor hm (σ i) x|) ∧
        ∀ (a δ : ℝ), 0 < δ → δ ≤ ε / 2 → ∀ (j : ℕ) (x : ℝ × Parameters 2 d),
          x ∈ tsupport (scaleTimeLocalizedCutoff (ψ i) a δ j) →
          ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ s ∈ uIcc (a + (j : ℝ) * δ) (a + (j : ℝ) * δ + δ * τ),
            (s, x.2) ∈ L i) ∧
      ∀ x, ∑ i : S, ψ i x = χ x := by
  classical
  obtain ⟨S, ψ, σ, b, hψ, hsum⟩ :=
    G.exists_finite_cinematicInitialMinor_cutoff_partition χ hχ hc hχ0 ha hdet m hm
  let U : S → Set (ℝ × Parameters 2 d) := fun i =>
    {x | AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x ∧
      b i / 2 < |G.cinematicInitialMinor hm (σ i) x|}
  have hU (i : S) : IsOpen (U i) := G.isOpen_cinematicInitialMinor_regular hm (σ i) (b i / 2)
  have hsub (i : S) : tsupport (ψ i) ⊆ U i := by
    obtain ⟨_, _, _, hb, hgood, _⟩ := hψ i
    intro x hx
    obtain ⟨hax, hbx⟩ := hgood x hx
    exact ⟨hax, by linarith⟩
  have hlocal (i : S) := exists_regular_scaleTimeLocalized_segments (ψ i) (hψ i).2.1 (hU i) (hsub i)
  choose ε L hε hL hψL hLU hspan using hlocal
  obtain ⟨r, hr, hrε⟩ := exists_common_time_scale_bound ε hε
  refine ⟨S, ψ, σ, (fun i => b i / 2), L, r, hr, ?_, hsum⟩
  intro i
  obtain ⟨hi, hci, hsχ, hb, _, hri⟩ := hψ i
  refine ⟨hi, hci, hsχ, hri, hL i, hψL i, half_pos hb, ?_, ?_⟩
  · intro x hx
    exact ⟨(hLU i hx).1, (hLU i hx).2.le⟩
  · intro a δ hδ hδr j x hx τ hτ s hs
    exact hspan i a δ hδ (hδr.trans (by linarith [hrε i])) j x hx τ hτ s hs

end PlanarNikodym
