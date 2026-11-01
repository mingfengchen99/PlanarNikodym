import PlanarNikodym.Cells.AnalyticRankCover
import PlanarNikodym.Classification.CountableFoliations

/-! D-R0: classification from countably many actual rank pieces whose
uncovered source has a closure with volume-null centre projection.
No finiteness, disjointness, definability or closed centre exception is
assumed. The geometric nullity hypothesis is explicit and is not proved
for arbitrary analytic families in this module. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

def Family.rankPieceRemainder {d : ℕ} (G : Family 2 d) (S : Set (RankPiece G)) :
    Set (Parameters 2 d) :=
  G.W \ ⋃ P : S, P.val.toAnalyticPiece.image

/-- Only the part of the source closure still lying in the parameter
domain matters; projection and closure are deliberately not interchanged. -/
def Family.rankPieceClosureCenters {d : ℕ} (G : Family 2 d) (S : Set (RankPiece G)) :
    Set (Base 2) :=
  Prod.fst '' (G.W ∩ closure (G.rankPieceRemainder S))

theorem Family.rankPiece_cover {d : ℕ} (G : Family 2 d) (S : Set (RankPiece G))
    (p : Parameters 2 d) (hp : p ∈ G.W) :
    p.1 ∈ G.rankPieceClosureCenters S ∨ ∃ P ∈ S, p ∈ P.toAnalyticPiece.image := by
  classical
  by_cases h : p ∈ ⋃ P : S, P.val.toAnalyticPiece.image
  · obtain ⟨P, hP⟩ := mem_iUnion.mp h
    exact Or.inr ⟨P.val, P.property, hP⟩
  · exact Or.inl ⟨p, ⟨hp, subset_closure ⟨hp, h⟩⟩, rfl⟩

def AnalyticRankCover.of_null_remainderClosure {d : ℕ} {G : Family 2 d}
    (S : Set (RankPiece G)) (hS : S.Countable)
    (hnull : volume (G.rankPieceClosureCenters S) = 0) : AnalyticRankCover G where
  pieces := S
  countable := hS
  exceptional := G.rankPieceClosureCenters S
  null_exceptional := hnull
  cover := G.rankPiece_cover S

/-- A common closed null centre container is sufficient, but stronger
than the source-closure hypothesis used in the classification theorem. -/
theorem Family.rankPieceClosureCenters_null_of_closed_exception {d : ℕ}
    (G : Family 2 d) (S : Set (RankPiece G)) (E : Set (Base 2))
    (hE : IsClosed E) (hnull : volume E = 0)
    (hcover : ∀ p ∈ G.W, p.1 ∈ E ∨ ∃ P ∈ S, p ∈ P.toAnalyticPiece.image) :
    volume (G.rankPieceClosureCenters S) = 0 := by
  apply measure_mono_null (t := E) ?_ hnull
  have hsub : G.rankPieceRemainder S ⊆ Prod.fst ⁻¹' E := by
    intro p hp
    rcases hcover p hp.1 with he | ⟨P, hP, hpP⟩
    · exact he
    · exact (hp.2 (mem_iUnion.mpr ⟨⟨P, hP⟩, hpP⟩)).elim
  rintro z ⟨p, hp, rfl⟩
  exact closure_minimal hsub (hE.preimage continuous_fst) hp.2

/-- Positive local H¹ reuse is caught by one actual piece in a parameter
neighbourhood avoiding the source remainder. Countable Borel centre
fibres and countable foliations are sufficient, including an empty S. -/
theorem Family.locallyReusedCovered_of_countable_rankPieces_strong {d : ℕ}
    (G : Family 2 d) (ha : G.IsAnalytic) (S : Set (RankPiece G)) (hS : S.Countable)
    (hnull : volume (G.rankPieceClosureCenters S) = 0)
    (hstrong : ∀ P ∈ S, P.family.ReusedStronglyCovered) : G.LocallyReusedCovered := by
  classical
  letI : Countable S := hS.to_subtype
  choose V hV using (fun P : S => hstrong P.val P.property)
  let fields := Family.Foliations.countableUnion V
  have hcover : ∀ p ∈ G.W, p.1 ∉ G.rankPieceClosureCenters S →
      G.LocallyReused p → G.Covered fields p := by
    intro p hp hpb hl
    have hpcl : p ∉ closure (G.rankPieceRemainder S) :=
      fun hc => hpb ⟨p, ⟨hp, hc⟩, rfl⟩
    let U := (closure (G.rankPieceRemainder S))ᶜ
    have hU : U ∈ 𝓝 p := isClosed_closure.isOpen_compl.mem_nhds hpcl
    have hpos := hl.2 U hU
    have hsub : Prod.fst '' (G.parametersOf (G.curve p) ∩ U) ⊆
        (∅ : Set (Base 2)) ∪ ⋃ P : S, P.val.family.centersOf (G.curve p) := by
      rintro z ⟨q, ⟨⟨hq, hqc⟩, hqU⟩, rfl⟩
      have hqcover : q ∈ ⋃ P : S, P.val.toAnalyticPiece.image := by
        by_contra hn
        exact hqU (subset_closure ⟨hq, hn⟩)
      obtain ⟨P, r, hr, hrq⟩ := mem_iUnion.mp hqcover
      have hzc : r.1 = q.1 :=
        (P.val.keep_center r hr).symm.trans (congrArg Prod.fst hrq)
      have hrc : P.val.family.curve r = G.curve p :=
        (P.val.toAnalyticPiece.curve_eq r hr).trans ((congrArg G.curve hrq).trans hqc)
      have hzr : r.1 ∈ P.val.family.centersOf (G.curve p) :=
        (P.val.family.mem_centersOf (G.curve p) r.1).mpr ⟨r.2, hr, hrc⟩
      exact Or.inr (mem_iUnion.mpr ⟨P, hzc ▸ hzr⟩)
    obtain ⟨P, hP⟩ := hpos.exists_of_countable_cover
      (fun P : S => P.val.family.centersOf (G.curve p))
      (fun P => P.val.centers_measurable (G.curve p)) hsub measure_empty
    obtain ⟨z, hz⟩ := hP.nonempty
    obtain ⟨u, hu, hc⟩ := (P.val.family.mem_centersOf (G.curve p) z).mp hz
    have hcov := hV P (z, u) hu (hc.symm ▸ hP)
    have hcovG := G.covered_of_curve_eq P.val.family ha.isSmooth p hp
      (z, u) (V P) hc.symm hcov
    exact G.covered_countableUnion V P p hcovG
  refine ⟨fields, measure_mono_null ?_ hnull⟩
  rintro z ⟨u, hl, hn⟩
  by_contra hb
  exact hn (hcover (z, u) hl.1 hb hl)

theorem Family.null_cover_of_countable_rankPieces {d : ℕ} (inputs : P5Inputs)
    (G : Family 2 d) (ha : G.IsAnalytic) (S : Set (RankPiece G)) (hS : S.Countable)
    (hnull : volume (G.rankPieceClosureCenters S) = 0) (hn : ¬ G.AdmitsNikodym) :
    G.LocallyReusedCovered := by
  apply G.locallyReusedCovered_of_countable_rankPieces_strong ha S hS hnull
  intro P _
  have hPn : ¬ P.family.AdmitsNikodym :=
    fun h => hn (P.family.admitsNikodym_mono G P.toAnalyticPiece.curves_mono h)
  have hc := constant_rank_classification inputs P.family P.connected_domain.nonempty
    P.open_domain P.analytic_family P.ranks
  exact constant_rank_strong_cover_of_negative inputs P.family P.connected_domain.nonempty
    P.open_domain P.analytic_family P.ranks
    (fun hm => hPn (hc.mpr (Or.inl hm))) (fun hu => hPn (hc.mpr (Or.inr hu)))

/-- The full classification, conditional only on actual countable pieces
with the stated geometric source-closure control and the P5 analysis. -/
theorem Family.classification_of_countable_rankPieces {d : ℕ} (inputs : P5Inputs)
    (G : Family 2 d) (ha : G.IsAnalytic) (S : Set (RankPiece G)) (hS : S.Countable)
    (hnull : volume (G.rankPieceClosureCenters S) = 0) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  constructor
  · exact (AnalyticRankCover.of_null_remainderClosure S hS hnull).classification_forward inputs
  · rintro (hm | hu)
    · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
    · by_contra hn
      exact G.not_localReuseNotCovered_of_null_cover
        (G.null_cover_of_countable_rankPieces inputs ha S hS hnull hn) hu

theorem AnalyticRankCover.remainderClosure_centers_null {d : ℕ} {G : Family 2 d}
    (D : AnalyticRankCover G) (hclosed : IsClosed D.exceptional) :
    volume (G.rankPieceClosureCenters D.pieces) = 0 :=
  G.rankPieceClosureCenters_null_of_closed_exception D.pieces D.exceptional
    hclosed D.null_exceptional D.cover

theorem RankDecomposition.rankPieceClosureCenters_null {d : ℕ} {G : Family 2 d}
    (D : RankDecomposition G) : volume (G.rankPieceClosureCenters (range D.piece)) = 0 := by
  apply G.rankPieceClosureCenters_null_of_closed_exception (range D.piece) D.exceptional
    D.closed_exceptional D.null_exceptional
  intro p hp
  rcases D.cover p hp with he | ⟨i, hi⟩
  · exact Or.inl he
  · exact Or.inr ⟨D.piece i, mem_range_self i, hi⟩

end PlanarNikodym
