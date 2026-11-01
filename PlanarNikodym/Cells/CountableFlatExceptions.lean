import PlanarNikodym.Cells.AnalyticFiberExceptions
import Mathlib.Topology.Compactness.Lindelof

/-! Flat auxiliary fibres on an open connected analytic domain admit a
null centre envelope. This is a countable union of local closed null
envelopes; no global closedness or null closure is asserted. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem exists_null_flat_auxiliary_fiber_exception {d : ℕ}
    {F : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (ho : IsOpen W) (hc : IsPreconnected W) (ha : AnalyticOnNhd ℝ F W)
    (hne : ∃ p ∈ W, F p ≠ 0) :
    ∃ E : Set (Base 2), volume E = 0 ∧
      ∀ p ∈ W, (∀ᶠ u in 𝓝 p.2, F (p.1, u) = 0) → p.1 ∈ E := by
  classical
  have hex (p : W) : ∃ (O : Set (Parameters 2 d)) (E : Set (Base 2)),
      IsOpen O ∧ (p : Parameters 2 d) ∈ O ∧ IsClosed E ∧ volume E = 0 ∧
      ∀ q ∈ O, (∀ᶠ u in 𝓝 q.2, F (q.1, u) = 0) → q.1 ∈ E := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds p.property)
    have hprod : ball p.val.1 r ×ˢ ball p.val.2 r ⊆ W := by
      rw [ball_prod_same]
      exact hball
    obtain ⟨E, hEc, hEn, hE⟩ := analytic_product_patch_flat_centers_closed_null ha hc hne
      isOpen_ball isOpen_ball ((convex_ball p.val.1 r).isConnected (nonempty_ball.mpr hr))
      ((convex_ball p.val.2 r).isConnected (nonempty_ball.mpr hr)) hprod
      (isCompact_closedBall p.val.1 (r / 2))
      (closedBall_subset_ball (half_lt_self hr))
    refine ⟨ball p.val.1 (r / 2) ×ˢ ball p.val.2 r, E,
      isOpen_ball.prod isOpen_ball, ⟨mem_ball_self (half_pos hr), mem_ball_self hr⟩,
      hEc, hEn, ?_⟩
    intro q hq hflat
    apply hE
    apply subset_closure
    exact ⟨ball_subset_closedBall hq.1,
      ball_subset_ball (half_le_self hr.le) hq.1, q.2, hq.2, hflat⟩
  choose O E hOo hpO hEc hEn hflat using hex
  obtain ⟨T, hTc, hcover⟩ := (HereditarilyLindelofSpace.isLindelof W).elim_countable_subcover
    O hOo (by intro p hp; exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpO ⟨p, hp⟩⟩)
  refine ⟨⋃ p ∈ T, E p, (measure_biUnion_null_iff hTc).mpr (fun p _ => hEn p), ?_⟩
  intro p hp hpf
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hcover hp)
  exact mem_iUnion₂.mpr ⟨q, hq, hflat q p hpq hpf⟩

end PlanarNikodym
