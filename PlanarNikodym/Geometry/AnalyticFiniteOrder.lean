import PlanarNikodym.Geometry.AnalyticCoordinateJets
import PlanarNikodym.Rank.GenericAnalyticRank

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

/-- A nontrivial analytic function on a connected domain has a finite
nonzero coordinate jet at every point, including singular zeroes. -/
theorem exists_nonzero_coordinateJet {n : ℕ} {f : Base n → ℝ}
    {W : Set (Base n)} (ha : AnalyticOnNhd ℝ f W) (hc : IsPreconnected W)
    (hne : ∃ q ∈ W, f q ≠ 0) {x : Base n} (hx : x ∈ W) :
    ∃ (k : ℕ) (s : Fin k → Fin n), coordinateJet f k s x ≠ 0 := by
  by_contra! hflat
  have he := ha.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    hc hx (analytic_eventually_zero_of_coordinateJets_zero (ha x hx) hflat)
  obtain ⟨q, hq, hnq⟩ := hne
  exact hnq (he hq)

/-- Finite-order nonflatness is uniform on each actual compact subset of
the analytic domain. No definability or order-bound field is assumed. -/
theorem exists_uniform_nonzero_coordinateJet_order {n : ℕ} {f : Base n → ℝ}
    {W K : Set (Base n)} (ho : IsOpen W) (ha : AnalyticOnNhd ℝ f W)
    (hc : IsPreconnected W) (hne : ∃ q ∈ W, f q ≠ 0)
    (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ N : ℕ, ∀ x ∈ K, ∃ k ≤ N, ∃ s : Fin k → Fin n, coordinateJet f k s x ≠ 0 := by
  classical
  choose k s hs using fun x : K => exists_nonzero_coordinateJet ha hc hne (hKW x.2)
  let O (x : K) := {y | y ∈ W ∧ coordinateJet f (k x) (s x) y ≠ 0}
  have hO (x : K) : IsOpen (O x) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact inter_mem (ho.mem_nhds hy.1)
      ((coordinateJet_analytic ha _ _ y hy.1).continuousAt.eventually_ne hy.2)
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover O hO (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hKW hx, hs ⟨x, hx⟩⟩)
  refine ⟨T.sup k, ?_⟩
  intro x hx
  obtain ⟨a, haT, hxa⟩ := mem_iUnion₂.mp (hT hx)
  exact ⟨k a, Finset.le_sup haT, s a, hxa.2⟩

/-- A possibly singular zero belongs to a regular zero set of an actual
coordinate derivative of the original function. The first-order
regularity assumption on the original function is eliminated. -/
theorem exists_regular_coordinateJet_at_zero {n : ℕ} {f : Base n → ℝ}
    {W : Set (Base n)} (ha : AnalyticOnNhd ℝ f W) (hc : IsPreconnected W)
    (hne : ∃ q ∈ W, f q ≠ 0) {x : Base n} (hx : x ∈ W) (hfx : f x = 0) :
    ∃ (k : ℕ) (s : Fin k → Fin n) (j : Fin n),
      coordinateJet f k s x = 0 ∧
        fderiv ℝ (coordinateJet f k s) x (Pi.single j 1) ≠ 0 := by
  classical
  have hex := exists_nonzero_coordinateJet ha hc hne hx
  let P (k : ℕ) := ∃ s : Fin k → Fin n, coordinateJet f k s x ≠ 0
  have hp : ∃ k, P k := hex
  have hkpos : 0 < Nat.find hp := by
    by_contra hn
    have hkzero : Nat.find hp = 0 := by omega
    have hz : P 0 := hkzero ▸ Nat.find_spec hp
    obtain ⟨s, hs⟩ := hz
    exact hs hfx
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hsucc : P (Nat.find hp) := Nat.find_spec hp
  rw [hk] at hsucc
  obtain ⟨s, hs⟩ := hsucc
  have hlow : coordinateJet f k (Fin.tail s) x = 0 := by
    by_contra hn
    have hmin := Nat.find_min' hp (show P k from ⟨Fin.tail s, hn⟩)
    omega
  refine ⟨k, Fin.tail s, s 0, hlow, ?_⟩
  have he := coordinateJet_cons ha (Fin.tail s) (s 0) hx
  rw [Fin.cons_self_tail] at he
  exact he ▸ hs

theorem analytic_zero_set_subset_regular_coordinateJets {n : ℕ} {f : Base n → ℝ}
    {W : Set (Base n)} (ha : AnalyticOnNhd ℝ f W) (hc : IsPreconnected W)
    (hne : ∃ q ∈ W, f q ≠ 0) :
    {x | x ∈ W ∧ f x = 0} ⊆
      ⋃ k, ⋃ s : Fin k → Fin n, ⋃ j : Fin n,
        {x | x ∈ W ∧ coordinateJet f k s x = 0 ∧
          fderiv ℝ (coordinateJet f k s) x (Pi.single j 1) ≠ 0} := by
  intro x hx
  obtain ⟨k, s, j, hz, hd⟩ := exists_regular_coordinateJet_at_zero ha hc hne hx.1 hx.2
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨j, hx.1, hz, hd⟩⟩⟩

end PlanarNikodym
