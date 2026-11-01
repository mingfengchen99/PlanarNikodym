import PlanarNikodym.Cells.AnalyticRankCoverAssembly
import PlanarNikodym.Cells.CountableRankStep
import PlanarNikodym.Classification.GeneralClassification

/-! Actual countable rank covers on arbitrary open analytic parameter
domains. Auxiliary dimension strictly decreases at every nonconstant-rank
branch. This construction supplies no finite or disjoint cell partition
and makes no closedness claim for the countable null centre exception. -/

noncomputable section
open Set MeasureTheory Metric
namespace PlanarNikodym

theorem Family.exists_analyticRankCover_connected (d : ℕ) (G : Family 2 d)
    (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic) :
    Nonempty (AnalyticRankCover G) := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain ⟨E, S, hE, hS, hP, hcover⟩ := G.exists_countable_rank_step ho hc ha
    letI : Countable S := hS.to_subtype
    have hchild (P : S) : Nonempty (AnalyticRankCover P.val.family) := by
      rcases (hP P.val P.property).2 with hl | ⟨mp, mc, hr⟩
      · exact ih P.val.dim hl P.val.family P.val.open_domain
          P.val.connected_domain P.val.analytic_family
      · exact ⟨AnalyticRankCover.ofFinite (RankDecomposition.single_proved P.val.family
          P.val.open_domain P.val.bounded_domain P.val.connected_domain P.val.analytic_family hr)⟩
    refine ⟨AnalyticRankCover.assemble (fun P : S => P.val) E hE ?_
      (fun P => Classical.choice (hchild P))⟩
    intro p hp
    rcases hcover p hp with he | ⟨P, hPS, hpP⟩
    · exact Or.inl he
    · exact Or.inr ⟨⟨P, hPS⟩, hpP⟩

/-- Every open real analytic family has an actual countable collection
of constant-rank centre-preserving analytic subfamilies covering all
parameters outside a volume-null set of centres. -/
theorem Family.exists_analyticRankCover {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    Nonempty (AnalyticRankCover G) := by
  classical
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_ball_parameter_cover G ho hne
    let O := C.toOpenParameterCover
    let P (i : ℕ) : AnalyticPiece G :=
      AnalyticPiece.restrict G (O.domain i) (O.isOpen i) isBounded_ball
        ((convex_ball (C.center i) (C.radius i)).isConnected
          ⟨C.center i, mem_ball_self (C.radius_pos i)⟩)
        (C.analyticAtClosure ha i).isAnalytic (O.subset i)
    have hchild (i : ℕ) : Nonempty (AnalyticRankCover (P i).family) :=
      Family.exists_analyticRankCover_connected d (P i).family (P i).open_domain
        (P i).connected_domain (P i).analytic_family
    refine ⟨AnalyticRankCover.assemble P ∅ measure_empty ?_
      (fun i => Classical.choice (hchild i))⟩
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (O.covers hp)
    exact Or.inr ⟨i, p, hi, rfl⟩
  · exact ⟨AnalyticRankCover.empty G (not_nonempty_iff_eq_empty.mp hne)⟩

end PlanarNikodym
