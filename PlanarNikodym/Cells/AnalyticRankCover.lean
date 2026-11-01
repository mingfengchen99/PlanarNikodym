import PlanarNikodym.Cells.DecompositionClassification

/-! Countable analytic rank covers and the conclusions that require only
volume-null exceptional centres. These covers allow overlaps and do not
assert closedness of the exception. They therefore do not replace the
finite compatible cell input, or the local-reuse argument using a closed
exception and positive one-dimensional Hausdorff measure. -/

noncomputable section
open Set MeasureTheory

namespace PlanarNikodym

structure AnalyticRankCover {d : ℕ} (G : Family 2 d) where
  pieces : Set (RankPiece G)
  countable : pieces.Countable
  exceptional : Set (Base 2)
  null_exceptional : volume exceptional = 0
  cover : ∀ p ∈ G.W, p.1 ∈ exceptional ∨
    ∃ P ∈ pieces, p ∈ P.toAnalyticPiece.image

namespace AnalyticRankCover
variable {d : ℕ} {G : Family 2 d} (D : AnalyticRankCover G)

theorem centers_cover (β : Set Plane) :
    G.centersOf β ⊆ D.exceptional ∪ ⋃ P : D.pieces, P.val.family.centersOf β := by
  intro z hz
  obtain ⟨u, hu, he⟩ := (G.mem_centersOf β z).mp hz
  rcases D.cover (z, u) hu with hb | ⟨P, hP, q, hq, hqe⟩
  · exact Or.inl hb
  · apply Or.inr
    have hzc : q.1 = z := (P.keep_center q hq).symm.trans (congrArg Prod.fst hqe)
    have hqc : P.family.curve q = β :=
      (P.toAnalyticPiece.curve_eq q hq).trans ((congrArg G.curve hqe).trans he)
    have hzq : q.1 ∈ P.family.centersOf β :=
      (P.family.mem_centersOf β q.1).mpr ⟨q.2, hq, hqc⟩
    exact mem_iUnion.mpr ⟨⟨P, hP⟩, hzc ▸ hzq⟩

theorem incidence_cover (E : Set Plane) :
    G.incidenceCenters G.W E ⊆ D.exceptional ∪
      ⋃ P : D.pieces, P.val.family.incidenceCenters P.val.family.W E := by
  rintro z ⟨u, hu, he⟩
  rcases D.cover (z, u) hu with hb | ⟨P, hP, q, hq, hqe⟩
  · exact Or.inl hb
  · apply Or.inr
    have hzc : q.1 = z := (P.keep_center q hq).symm.trans (congrArg Prod.fst hqe)
    have hqc : P.family.curve q = G.curve (z, u) :=
      (P.toAnalyticPiece.curve_eq q hq).trans (congrArg G.curve hqe)
    have hzq : q.1 ∈ P.family.incidenceCenters P.family.W E :=
      ⟨q.2, hq, by rwa [hqc]⟩
    exact mem_iUnion.mpr ⟨⟨P, hP⟩, hzc ▸ hzq⟩

theorem incidence_null_of_no_piece (inputs : P5Inputs)
    (hn : ∀ P ∈ D.pieces, ¬ P.family.AdmitsNikodym) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  letI : Countable D.pieces := D.countable.to_subtype
  intro E hE hE0
  apply measure_mono_null (D.incidence_cover E)
  apply measure_union_null D.null_exceptional
  apply measure_iUnion_null
  intro P
  exact constant_rank_incidence_null_of_noNikodym inputs P.val.family
    P.val.connected_domain.nonempty P.val.open_domain P.val.analytic_family
    P.val.ranks (hn P.val P.property) E hE hE0

theorem admitsNikodym_iff (inputs : P5Inputs) :
    G.AdmitsNikodym ↔ ∃ P ∈ D.pieces, P.family.AdmitsNikodym := by
  constructor
  · intro hG
    by_contra hn
    exact G.no_nikodym_of_incidence_null
      (D.incidence_null_of_no_piece inputs (fun P hP hi => hn ⟨P, hP, hi⟩)) hG
  · rintro ⟨P, _, hi⟩
    exact P.family.admitsNikodym_mono G P.toAnalyticPiece.curves_mono hi

theorem hasMassiveCurveReuse_iff :
    G.HasMassiveCurveReuse ↔ ∃ P ∈ D.pieces, P.family.HasMassiveCurveReuse := by
  letI : Countable D.pieces := D.countable.to_subtype
  constructor
  · rintro ⟨β, hβ⟩
    obtain ⟨P, hi⟩ := hβ.exists_of_countable_cover
      (fun P : D.pieces => P.val.family.centersOf β)
      (fun P => P.val.centers_measurable β) (D.centers_cover β) D.null_exceptional
    exact ⟨P.val, P.property, β, hi⟩
  · rintro ⟨P, _, hi⟩
    exact P.family.hasMassiveCurveReuse_mono G P.toAnalyticPiece.curves_mono hi

include D in
theorem centers_nullMeasurable (β : Set Plane) :
    NullMeasurableSet (G.centersOf β) volume := by
  letI : Countable D.pieces := D.countable.to_subtype
  let S := ⋃ P : D.pieces, P.val.family.centersOf β
  have hS : MeasurableSet S :=
    MeasurableSet.iUnion (fun P : D.pieces => P.val.centers_measurable β)
  apply hS.nullMeasurableSet.congr
  filter_upwards [compl_mem_ae_iff.mpr D.null_exceptional] with z hz
  apply propext
  constructor
  · intro hs
    obtain ⟨P, hi⟩ := mem_iUnion.mp hs
    exact P.val.family.centersOf_mono G P.val.toAnalyticPiece.curves_mono β hi
  · intro hg
    exact (D.centers_cover β hg).resolve_left hz

include D in
/-- The forward classification implication needs countability and nullity
only. The converse is deliberately not asserted for this certificate. -/
theorem classification_forward (inputs : P5Inputs) :
    G.AdmitsNikodym → G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  intro hG
  obtain ⟨P, hP, hi⟩ := (D.admitsNikodym_iff inputs).mp hG
  rcases (constant_rank_classification inputs P.family
    P.connected_domain.nonempty P.open_domain P.analytic_family P.ranks).mp hi with hm | hu
  · exact Or.inl ((D.hasMassiveCurveReuse_iff).mpr ⟨P, hP, hm⟩)
  · exact Or.inr (P.toAnalyticPiece.localReuseNotCovered_mono hu)

include D in
theorem incidence_null_of_noNikodym (inputs : P5Inputs) (hn : ¬ G.AdmitsNikodym) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 :=
  D.incidence_null_of_no_piece inputs
    (fun P hP hi => hn ((D.admitsNikodym_iff inputs).mpr ⟨P, hP, hi⟩))

end AnalyticRankCover
end PlanarNikodym
