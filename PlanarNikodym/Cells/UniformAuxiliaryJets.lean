import PlanarNikodym.Cells.AuxiliarySingularJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology

namespace PlanarNikodym

/-- On an actual compact set of nonflat fibres, a single finite auxiliary
jet order suffices. Compactness is used after excluding flat fibres; a
bound for joint centre/auxiliary jets would not imply this statement. -/
theorem exists_uniform_auxiliaryJet_order_of_nonflat {d : ℕ}
    {f : Parameters 2 d → ℝ} {W K : Set (Parameters 2 d)}
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (hK : IsCompact K) (hKW : K ⊆ W)
    (hnf : ∀ p ∈ K, ¬ ∀ᶠ u in 𝓝 p.2, f (p.1, u) = 0) :
    ∃ N : ℕ, ∀ p ∈ K, ∃ k ≤ N, ∃ s : Fin k → Fin d,
      auxiliaryJet f k s p ≠ 0 := by
  classical
  have hex (p : K) : ∃ (k : ℕ) (s : Fin k → Fin d), auxiliaryJet f k s p ≠ 0 := by
    by_contra! hz
    exact hnf p p.2 (analytic_eventually_zero_of_coordinateJets_zero
      (analytic_auxiliary_slice ha p.1.1 p.1.2 (hKW p.2)) hz)
  choose k s hs using hex
  let O (p : K) := {q | q ∈ W ∧ auxiliaryJet f (k p) (s p) q ≠ 0}
  have hO (p : K) : IsOpen (O p) := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact inter_mem (ho.mem_nhds hq.1)
      ((auxiliaryJet_analytic ho ha _ _ q hq.1).continuousAt.eventually_ne hq.2)
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover O hO (by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hKW hp, hs ⟨p, hp⟩⟩)
  refine ⟨T.sup k, ?_⟩
  intro p hp
  obtain ⟨q, hqT, hpq⟩ := mem_iUnion₂.mp (hT hp)
  exact ⟨k q, Finset.le_sup hqT, s q, hpq.2⟩

/-- A finite nonzero auxiliary jet gives a strictly lower order regular
zero jet. The order bound is retained explicitly. -/
theorem exists_regular_auxiliaryJet_below {d N : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    {p : Parameters 2 d} (hp : p ∈ W) (hz : f p = 0)
    (hN : ∃ k ≤ N, ∃ s : Fin k → Fin d, auxiliaryJet f k s p ≠ 0) :
    ∃ k < N, ∃ (s : Fin k → Fin d) (j : Fin d),
      auxiliaryJet f k s p = 0 ∧
        fderiv ℝ (auxiliaryJet f k s) p (0, Pi.single j 1) ≠ 0 := by
  classical
  let P (k : ℕ) := ∃ s : Fin k → Fin d, auxiliaryJet f k s p ≠ 0
  obtain ⟨m, hmN, hm⟩ := hN
  have hex : ∃ k, P k := ⟨m, hm⟩
  have hminN : Nat.find hex ≤ N := (Nat.find_min' hex hm).trans hmN
  have hpos : 0 < Nat.find hex := by
    by_contra hn
    have he : Nat.find hex = 0 := by omega
    have hzero : P 0 := he ▸ Nat.find_spec hex
    obtain ⟨s, hs⟩ := hzero
    exact hs hz
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hsucc : P (Nat.find hex) := Nat.find_spec hex
  rw [hk] at hsucc
  obtain ⟨s, hs⟩ := hsucc
  have hlow : auxiliaryJet f k (Fin.tail s) p = 0 := by
    by_contra hn
    have hmin := Nat.find_min' hex (show P k from ⟨Fin.tail s, hn⟩)
    omega
  refine ⟨k, by omega, Fin.tail s, s 0, hlow, ?_⟩
  have he := auxiliaryJet_cons_of_differentiable ha (Fin.tail s) (s 0) hp
    (auxiliaryJet_analytic ho ha k (Fin.tail s) p hp).differentiableAt
  rw [Fin.cons_self_tail] at he
  exact he ▸ hs

/-- A compact nonflat zero set is contained in the regular zero loci of
a finite pool of auxiliary jets. These loci are not asserted to be
compact, connected, disjoint, or single analytic charts. -/
theorem exists_uniform_regular_auxiliaryJet_order {d : ℕ}
    {f : Parameters 2 d → ℝ} {W K : Set (Parameters 2 d)}
    (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (hK : IsCompact K) (hKW : K ⊆ W)
    (hnf : ∀ p ∈ K, ¬ ∀ᶠ u in 𝓝 p.2, f (p.1, u) = 0) :
    ∃ N : ℕ, ∀ p ∈ K, f p = 0 →
      ∃ k < N, ∃ (s : Fin k → Fin d) (j : Fin d),
        auxiliaryJet f k s p = 0 ∧
          fderiv ℝ (auxiliaryJet f k s) p (0, Pi.single j 1) ≠ 0 := by
  obtain ⟨N, hN⟩ := exists_uniform_auxiliaryJet_order_of_nonflat ho ha hK hKW hnf
  exact ⟨N, fun p hp hz => exists_regular_auxiliaryJet_below ho ha (hKW hp) hz (hN p hp)⟩

end PlanarNikodym
