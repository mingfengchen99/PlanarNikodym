import PlanarNikodym.Cells.AnalyticRankCover
import PlanarNikodym.Cells.ReducedGeometry

/-! Assembly of countable analytic rank covers. Countable null exceptions
are combined by measure subadditivity, without an assertion that the
resulting exceptional set is closed. -/

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym
namespace AnalyticRankCover

def ofFinite {d : ℕ} {G : Family 2 d} (D : RankDecomposition G) :
    AnalyticRankCover G where
  pieces := range D.piece
  countable := countable_range D.piece
  exceptional := D.exceptional
  null_exceptional := D.null_exceptional
  cover := by
    intro p hp
    rcases D.cover p hp with he | ⟨i, hi⟩
    · exact Or.inl he
    · exact Or.inr ⟨D.piece i, mem_range_self i, hi⟩

def empty {d : ℕ} (G : Family 2 d) (hW : G.W = ∅) : AnalyticRankCover G where
  pieces := ∅
  countable := countable_empty
  exceptional := ∅
  null_exceptional := measure_empty
  cover := by simp [hW]

/-- Compose a countable cover of analytic pieces with countable rank
covers of their actual subfamilies. Overlap is allowed throughout. -/
def assemble {d : ℕ} {G : Family 2 d} {ι : Type*} [Countable ι]
    (P : ι → AnalyticPiece G) (E : Set (Base 2)) (hE : volume E = 0)
    (hcover : ∀ p ∈ G.W, p.1 ∈ E ∨ ∃ i, p ∈ (P i).image)
    (D : ∀ i, AnalyticRankCover (P i).family) : AnalyticRankCover G where
  pieces := ⋃ i, RankPiece.comp (P i) '' (D i).pieces
  countable := countable_iUnion (fun i => (D i).countable.image _)
  exceptional := E ∪ ⋃ i, (D i).exceptional
  null_exceptional := measure_union_null hE (measure_iUnion_null (fun i => (D i).null_exceptional))
  cover := by
    intro p hp
    rcases hcover p hp with he | ⟨i, q, hq, hqp⟩
    · exact Or.inl (Or.inl he)
    · rcases (D i).cover q hq with he | ⟨Q, hQ, r, hr, hrq⟩
      · apply Or.inl
        apply Or.inr
        have hz : p.1 = q.1 :=
          (congrArg Prod.fst hqp).symm.trans ((P i).keep_center q hq)
        rw [hz]
        exact mem_iUnion.mpr ⟨i, he⟩
      · apply Or.inr
        refine ⟨RankPiece.comp (P i) Q, mem_iUnion.mpr ⟨i, Q, hQ, rfl⟩, r, hr, ?_⟩
        change (P i).embed (Q.embed r) = p
        rw [hrq, hqp]

end AnalyticRankCover
end PlanarNikodym
