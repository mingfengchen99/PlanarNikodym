import PlanarNikodym.Cells.ControlledIntrinsicRankCover
import PlanarNikodym.Classification.CoordinateBallCover
import PlanarNikodym.Classification.ControlledRankClassification

/-! D-R5: the general analytic classification with all geometric and
analytic inputs constructed. Interior coordinate balls localize the
common closed exception; no closure of a countable union is taken. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem CoordinateBallParameterCover.exists_controlled_rank_pieces
    {d : ℕ} {G : Family 2 d} (C : CoordinateBallParameterCover G)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (i : ℕ) :
    ∃ S : Set (RankPiece (C.toOpenParameterCover.family i)), S.Countable ∧
      volume ((C.toOpenParameterCover.family i).rankPieceClosureCenters S) = 0 := by
  obtain ⟨D, hc, _⟩ := G.exists_controlled_rank_cover_on_coordinate_ball ho ha
    (C.center i) (C.radius i) (C.radius_pos i) (C.closure_subset i)
  exact ⟨D.pieces, D.countable, D.remainderClosure_centers_null hc.isClosed⟩

theorem Family.general_null_cover_proved {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (hn : ¬ G.AdmitsNikodym) :
    G.LocallyReusedCovered := by
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_coordinate_ball_parameter_cover G ho hne
    exact C.toOpenParameterCover.null_cover_of_controlled_rankPieces ha
      (C.exists_controlled_rank_pieces ho ha) hn
  · refine ⟨Family.Foliations.zero, ?_⟩
    have he : G.uncoveredLocalCenters Family.Foliations.zero = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro z ⟨u, hu, _⟩
      exact hne ⟨(z, u), hu.1⟩
    rw [he]
    exact measure_empty

theorem Family.general_classification_proved {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_coordinate_ball_parameter_cover G ho hne
    exact C.toOpenParameterCover.classification_of_controlled_rankPieces ho ha
      (C.exists_controlled_rank_pieces ho ha)
  · exact G.classification_of_empty (not_nonempty_iff_eq_empty.mp hne)

theorem theorem_1_4_proved : Theorem14Statement := by
  intro d G ho ha
  exact G.general_classification_proved ho ha.isAnalytic

end PlanarNikodym
