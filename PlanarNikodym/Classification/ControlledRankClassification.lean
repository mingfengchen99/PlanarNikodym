import PlanarNikodym.Cells.CountableRankClassification
import PlanarNikodym.Classification.AnalyticCountableConsequences

/-! D-R0 with the proved P5 analysis and the original general-classification
quantifiers. All remaining assumptions below are explicit geometric
covering/nullity statements; none asserts a classification conclusion. -/

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.null_cover_of_countable_rankPieces_proved {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (S : Set (RankPiece G)) (hS : S.Countable)
    (hnull : volume (G.rankPieceClosureCenters S) = 0) (hn : ¬ G.AdmitsNikodym) :
    G.LocallyReusedCovered :=
  G.null_cover_of_countable_rankPieces p5_inputs_proved ha S hS hnull hn

theorem Family.classification_of_countable_rankPieces_proved {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (S : Set (RankPiece G)) (hS : S.Countable)
    (hnull : volume (G.rankPieceClosureCenters S) = 0) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered :=
  G.classification_of_countable_rankPieces p5_inputs_proved ha S hS hnull

/-- The source-closure control may be constructed separately on each
member of an open cover. No control of the closure of the union of all
local centre exceptions is required. -/
theorem OpenParameterCover.null_cover_of_controlled_rankPieces {d : ℕ} {G : Family 2 d}
    (C : OpenParameterCover G) (ha : G.IsAnalytic)
    (hcover : ∀ i, ∃ S : Set (RankPiece (C.family i)), S.Countable ∧
      volume ((C.family i).rankPieceClosureCenters S) = 0)
    (hn : ¬ G.AdmitsNikodym) : G.LocallyReusedCovered := by
  apply C.locallyReusedCovered
  intro i
  obtain ⟨S, hS, hnull⟩ := hcover i
  apply (C.family i).null_cover_of_countable_rankPieces_proved
    (ha.restrictTo (C.subset i)) S hS hnull
  exact fun hi => hn ((C.family i).admitsNikodym_mono G (C.curves_mono i) hi)

theorem OpenParameterCover.classification_of_controlled_rankPieces {d : ℕ} {G : Family 2 d}
    (C : OpenParameterCover G) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (hcover : ∀ i, ∃ S : Set (RankPiece (C.family i)), S.Countable ∧
      volume ((C.family i).rankPieceClosureCenters S) = 0) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  constructor
  · exact G.general_classification_forward_proved ho ha
  · rintro (hm | hu)
    · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
    · by_contra hn
      exact G.not_localReuseNotCovered_of_null_cover
        (C.null_cover_of_controlled_rankPieces ha hcover hn) hu

/-- Exact Theorem 1.4 follows once the geometric controlled-cover property
has been constructed on the bounded analytic seeds. This is an adapter,
not a proof of that remaining geometric existence statement. -/
theorem theorem_1_4_of_bounded_controlled_rankPieces
    (hgeometry : ∀ (d : ℕ) (G : Family 2 d),
      AnalyticParameterDomain G → G.IsAnalyticAtClosure →
      ∃ S : Set (RankPiece G), S.Countable ∧ volume (G.rankPieceClosureCenters S) = 0) :
    Theorem14Statement := by
  intro d G ho ha
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_ball_parameter_cover G ho hne
    apply C.toOpenParameterCover.classification_of_controlled_rankPieces ho ha.isAnalytic
    intro i
    exact hgeometry d (C.toOpenParameterCover.family i)
      (C.analytic_domain i) (C.analyticAtClosure ha.isAnalytic i)
  · exact G.classification_of_empty (not_nonempty_iff_eq_empty.mp hne)

end PlanarNikodym
