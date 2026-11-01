import PlanarNikodym.Cells.CountableAuxiliaryCharts
import PlanarNikodym.Cells.CountableFlatExceptions
import PlanarNikodym.Cells.MinorPatchResolution

/-! An actual countable rank-reduction step for an open connected analytic
family. Retained charts may overlap, and the null centre exception need
not be closed. This is not a finite compatible-cell input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym
set_option maxHeartbeats 800000

/-- On an open constant-rank locus, actual small balls have tame analytic
closures and give a countable family of full-dimensional rank pieces. -/
theorem exists_countable_regular_rank_pieces {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) {D : Set (Parameters 2 d)}
    (ho : IsOpen D) (hDW : D ⊆ G.W) {mp mc : ℕ}
    (hrank : ∀ p ∈ D, G.pointRank p = mp ∧ G.curveRank p = mc) :
    ∃ S : Set (AnalyticPiece G), S.Countable ∧
      (∀ P ∈ S, P.dim = d ∧ P.family.RanTame ∧ ConstantRanks P.family mp mc) ∧
      ∀ p ∈ D, ∃ P ∈ S, p ∈ P.image := by
  classical
  have hex (p : D) : ∃ (P : AnalyticPiece G) (U : Set (Parameters 2 d)),
      P.dim = d ∧ P.family.RanTame ∧ ConstantRanks P.family mp mc ∧
      IsOpen U ∧ (p : Parameters 2 d) ∈ U ∧ U ⊆ P.image := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds p.property)
    let U := ball (p : Parameters 2 d) (r / 2)
    have hcl : closure U ⊆ D := closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self hr)).trans hball)
    have hUD : U ⊆ D := subset_closure.trans hcl
    let H := G.restrictTo U
    have hHa : H.IsAnalyticAtClosure := by
      intro x hx
      exact ha x ⟨hx.1, hDW (hcl hx.2)⟩
    have hH : H.IsAnalytic := by
      intro x hx
      exact hHa x ⟨hx.1, subset_closure hx.2⟩
    let P : AnalyticPiece G := AnalyticPiece.restrict G U isOpen_ball isBounded_ball
      ((convex_ball (p : Parameters 2 d) (r / 2)).isConnected (nonempty_ball.mpr (half_pos hr)))
      hH (hUD.trans hDW)
    have ht : H.RanTame := H.ranTame_seed_ball p.val (r / 2) rfl hHa
    have hrP : ConstantRanks H mp mc := by
      intro q hq
      exact hrank q (hUD hq)
    exact ⟨P, U, rfl, ht, hrP, isOpen_ball, mem_ball_self (half_pos hr),
      fun q hq => ⟨q, hq, rfl⟩⟩
  choose P U hdim htame hrankP hUo hpU hUsub using hex
  obtain ⟨T, hTc, hcover⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover
    U hUo (by intro p hp; exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpU ⟨p, hp⟩⟩)
  refine ⟨P '' T, hTc.image P, ?_, ?_⟩
  · rintro Q ⟨q, _, rfl⟩
    exact ⟨hdim q, htame q, hrankP q⟩
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hcover hp)
    exact ⟨P q, mem_image_of_mem P hq, hUsub q hpq⟩

/-- Includes auxiliary dimension zero: every zero is then flat, so the
non-flat locus is empty and no lower-dimensional chart is needed. -/
theorem exists_countable_nonflat_auxiliary_zero_lower_pieces {d : ℕ}
    (G : Family 2 d) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (F : Parameters 2 d → ℝ) (hF : AnalyticOnNhd ℝ F G.W) :
    ∃ S : Set (AnalyticPiece G), S.Countable ∧
      (∀ P ∈ S, P.dim < d ∧ P.family.RanTame) ∧
      ∀ p ∈ G.W, F p = 0 → (¬ ∀ᶠ u in 𝓝 p.2, F (p.1, u) = 0) →
        ∃ P ∈ S, p ∈ P.image := by
  cases d with
  | zero =>
    refine ⟨∅, countable_empty, by simp, ?_⟩
    intro p _ hz hn
    apply (hn ?_).elim
    exact Filter.Eventually.of_forall fun u => by
      have he : u = p.2 := Subsingleton.elim _ _
      simpa only [he] using hz
  | succ d =>
    obtain ⟨S, hSc, hS, hcover⟩ := exists_countable_nonflat_auxiliary_zero_pieces G ho ha F hF
    refine ⟨S, hSc, ?_, hcover⟩
    intro P hP
    refine ⟨?_, (hS P hP).2.1⟩
    rw [(hS P hP).1]
    exact Nat.lt_succ_self d

/-- No tame premise is needed: tameness of each retained ball or implicit
chart is constructed from its actual analytic germ. The exception is
only null, not asserted closed, and pieces need not be disjoint. -/
theorem Family.exists_countable_rank_step {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic) :
    ∃ (E : Set (Base 2)) (S : Set (AnalyticPiece G)),
      volume E = 0 ∧ S.Countable ∧
      (∀ P ∈ S, P.family.RanTame ∧
        (P.dim < d ∨ ∃ mp mc : ℕ, ConstantRanks P.family mp mc)) ∧
      ∀ p ∈ G.W, p.1 ∈ E ∨ ∃ P ∈ S, p ∈ P.image := by
  classical
  obtain ⟨M, _, _, hMo, hMd, hMr⟩ := generic_double_rank_minor G ho hc ha
  have hFa := M.productValue_analytic ho ha
  have hFn := M.productValue_nontrivial hc hMd
  obtain ⟨E, hEn, hflat⟩ := exists_null_flat_auxiliary_fiber_exception ho hc.isPreconnected hFa hFn
  obtain ⟨Slo, hSloc, hSlo, hlocover⟩ :=
    exists_countable_nonflat_auxiliary_zero_lower_pieces G ho ha M.productValue hFa
  obtain ⟨Shi, hShic, hShi, hhicover⟩ := exists_countable_regular_rank_pieces G ha hMo
    (fun p hp => hp.1) hMr
  refine ⟨E, Slo ∪ Shi, hEn, hSloc.union hShic, ?_, ?_⟩
  · intro P hP
    rcases hP with hP | hP
    · exact ⟨(hSlo P hP).2, Or.inl (hSlo P hP).1⟩
    · exact ⟨(hShi P hP).2.1, Or.inr ⟨M.point.size, M.curve.size, (hShi P hP).2.2⟩⟩
  · intro p hp
    by_cases hreg : p ∈ M.regularSet
    · obtain ⟨P, hP, hpP⟩ := hhicover p hreg
      exact Or.inr ⟨P, Or.inr hP, hpP⟩
    · have hz : M.productValue p = 0 := by
        by_contra hn
        exact hreg ((M.mem_regularSet_iff_product p).mpr ⟨hp, hn⟩)
      by_cases hf : ∀ᶠ u in 𝓝 p.2, M.productValue (p.1, u) = 0
      · exact Or.inl (hflat p hp hf)
      · obtain ⟨P, hP, hpP⟩ := hlocover p hp hz hf
        exact Or.inr ⟨P, Or.inl hP, hpP⟩

end PlanarNikodym
