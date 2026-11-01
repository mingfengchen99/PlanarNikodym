import PlanarNikodym.Cells.CompactMinorResolution

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric MeasureTheory
open scoped Topology

namespace PlanarNikodym

/-- A product neighbourhood and its compact centre container are chosen
from openness. No product patch is an additional input to this theorem. -/
theorem DoubleRankMinor.exists_local_flat_exception {d : ℕ}
    {G : Family 2 d} (M : DoubleRankMinor G)
    (hG : G.RanTame) (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic)
    (hM : G.W ⊆ closure M.regularSet) {p : Parameters 2 d} (hp : p ∈ G.W) :
    ∃ O : Set (Parameters 2 d), ∃ E : Set (Base 2),
      IsOpen O ∧ p ∈ O ∧ O ⊆ G.W ∧ RanDefinable E ∧ IsClosed E ∧ volume E = 0 ∧
        ∀ q ∈ O, q.1 ∉ E → ¬ ∀ᶠ u in 𝓝 q.2, M.productValue (q.1, u) = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hp)
  let V := ball p.1 r
  let U := ball p.2 r
  let K := closedBall p.1 (r / 2)
  have hVU : V ×ˢ U ⊆ G.W := by
    simpa only [V, U, ball_prod_same] using hball
  have hcV : IsConnected V :=
    (convex_ball p.1 r).isConnected ⟨p.1, mem_ball_self hr⟩
  have hcU : IsConnected U :=
    (convex_ball p.2 r).isConnected ⟨p.2, mem_ball_self hr⟩
  have hKV : K ⊆ V := closedBall_subset_ball (half_lt_self hr)
  have hKd : RanDefinable K := by
    rw [show K = closure (ball p.1 (r / 2)) from (closure_ball _ (half_pos hr).ne').symm]
    exact RanDefinable.closure (ranDefinable_ball _ _)
  have hFa := M.productValue_analytic ho ha
  have hnonzero := exists_nonzero_on_analytic_product_patch hFa hc.isPreconnected
    (M.productValue_nontrivial hc hM) isOpen_ball isOpen_ball hcV.nonempty hcU.nonempty hVU
  have hD := ranDefinable_parameter_product (ranDefinable_ball p.1 r) (ranDefinable_ball p.2 r)
  have hFd := (M.productValue_definable hG ho ha).restrict hD (fun _ hx => hVU hx)
  obtain ⟨E, hEd, hEc, hEn, hEcover⟩ :=
    exists_ranDefinable_closed_null_flat_fiber_exception
      (ranDefinable_ball p.1 r) (ranDefinable_ball p.2 r) isOpen_ball isOpen_ball hcV hcU
      (hFa.mono hVU) hFd hnonzero (isCompact_closedBall _ _) hKV hKd
  let O := ball p.1 (r / 2) ×ˢ U
  have hOK : O ⊆ K ×ˢ U := fun _ hq => ⟨ball_subset_closedBall hq.1, hq.2⟩
  refine ⟨O, E, isOpen_ball.prod isOpen_ball,
    ⟨mem_ball_self (half_pos hr), mem_ball_self hr⟩,
    (fun q hq => hVU ⟨hKV (hOK hq).1, hq.2⟩), hEd, hEc, hEn, ?_⟩
  intro q hq hqE hflat
  have hz : q.1 ∈ K ∩ flatFiberCenters M.productValue V U :=
    ⟨(hOK hq).1, hKV (hOK hq).1, q.2, hq.2, hflat⟩
  exact hqE (hEcover (subset_closure hz))

/-- Finite patch selection gives one actual definable closed null centre
exception for every compact parameter set. The set need not be
definable. This is a finite union of exceptions, not a finite cell cover. -/
theorem DoubleRankMinor.exists_compact_exception_and_nonflat {d : ℕ}
    {G : Family 2 d} (M : DoubleRankMinor G)
    (hG : G.RanTame) (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic)
    (hM : G.W ⊆ closure M.regularSet) {L : Set (Parameters 2 d)}
    (hL : IsCompact L) (hLW : L ⊆ G.W) :
    ∃ E : Set (Base 2), RanDefinable E ∧ IsClosed E ∧ volume E = 0 ∧
      ∀ p ∈ L, p.1 ∉ E → ¬ ∀ᶠ u in 𝓝 p.2, M.productValue (p.1, u) = 0 := by
  classical
  choose O E hOo hpO hOW hEd hEc hEn hnf using
    fun p : L => M.exists_local_flat_exception hG ho hc ha hM (hLW p.2)
  obtain ⟨T, hT⟩ := hL.elim_finite_subcover O hOo (by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpO ⟨p, hp⟩⟩)
  refine ⟨⋃ i : T, E i.1,
    Set.definable_iUnion_of_finite (fun i : T => hEd i.1),
    isClosed_iUnion_of_finite (fun i : T => hEc i.1),
    measure_iUnion_null (fun i : T => hEn i.1), ?_⟩
  intro p hp hpE
  obtain ⟨i, hiT, hpi⟩ := mem_iUnion₂.mp (hT hp)
  apply hnf i p hpi
  intro hz
  exact hpE (mem_iUnion.mpr ⟨⟨i, hiT⟩, hz⟩)

/-- Actual rank-minor resolution on an arbitrary compact parameter set,
with no supplied product boxes, exceptional set, or jet-order bound.
The finite number of selected neighbourhoods controls the exception,
not the number of dimension-dropping analytic pieces. -/
theorem DoubleRankMinor.exists_compact_exception_pieces_and_order {d : ℕ}
    {G : Family 2 (d + 1)} (M : DoubleRankMinor G)
    (hG : G.RanTame) (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic)
    (hM : G.W ⊆ closure M.regularSet) {L : Set (Parameters 2 (d + 1))}
    (hL : IsCompact L) (hLW : L ⊆ G.W) :
    ∃ E : Set (Base 2), RanDefinable E ∧ IsClosed E ∧ volume E = 0 ∧
      (∀ p ∈ L, p.1 ∉ E → p ∉ M.regularSet →
        ∃ P : AnalyticPiece G, P.dim = d ∧ P.family.RanTame ∧ p ∈ P.image) ∧
      (∀ S : Set (Parameters 2 (d + 1)), IsCompact S → S ⊆ L →
        (∀ p ∈ S, p.1 ∉ E) →
        ∃ N : ℕ, ∀ p ∈ S, p ∉ M.regularSet →
          ∃ k < N, ∃ (s : Fin k → Fin (d + 1)) (j : Fin (d + 1)),
            auxiliaryJet M.productValue k s p = 0 ∧
              fderiv ℝ (auxiliaryJet M.productValue k s) p (0, Pi.single j 1) ≠ 0) := by
  obtain ⟨E, hEd, hEc, hEn, hnf⟩ :=
    M.exists_compact_exception_and_nonflat hG ho hc ha hM hL hLW
  have hFa := M.productValue_analytic ho ha
  have hzero (p : Parameters 2 (d + 1)) (hp : p ∈ L) (hpD : p ∉ M.regularSet) :
      M.productValue p = 0 := by
    by_contra hn
    exact hpD ((M.mem_regularSet_iff_product p).mpr ⟨hLW hp, hn⟩)
  refine ⟨E, hEd, hEc, hEn, ?_, ?_⟩
  · intro p hp hpE hpD
    rcases auxiliary_zero_flat_or_lower_piece G ho ha M.productValue hFa
        (hLW hp) (hzero p hp hpD) with hflat | ⟨P, hd, ht, hpP, _⟩
    · exact (hnf p hp hpE hflat).elim
    · exact ⟨P, hd, ht, hpP⟩
  · intro S hS hSL hSE
    obtain ⟨N, hN⟩ := exists_uniform_regular_auxiliaryJet_order ho hFa hS
      (hSL.trans hLW) (fun p hp => hnf p (hSL hp) (hSE p hp))
    exact ⟨N, fun p hp hpD => hN p hp (hzero p (hSL hp) hpD)⟩

end PlanarNikodym
