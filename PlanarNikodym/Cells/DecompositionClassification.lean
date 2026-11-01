import PlanarNikodym.Cells.RankDecomposition
import PlanarNikodym.Classification.ConstantRankConsequences

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym
namespace RankDecomposition
variable {d : ℕ} {G : Family 2 d} (D : RankDecomposition G)

theorem centers_cover (β : Set Plane) :
    G.centersOf β ⊆ D.exceptional ∪ ⋃ i, (D.piece i).family.centersOf β := by
  intro z hz
  obtain ⟨u, hu, he⟩ := (G.mem_centersOf β z).mp hz
  rcases D.cover (z, u) hu with hb | ⟨i, q, hq, hqe⟩
  · exact Or.inl hb
  · apply Or.inr
    apply mem_iUnion.mpr
    have hzc : q.1 = z := ((D.piece i).keep_center q hq).symm.trans (congrArg Prod.fst hqe)
    have hqc : (D.piece i).family.curve q = β :=
      ((D.piece i).toAnalyticPiece.curve_eq q hq).trans ((congrArg G.curve hqe).trans he)
    have hzq : q.1 ∈ (D.piece i).family.centersOf β :=
      ((D.piece i).family.mem_centersOf β q.1).mpr ⟨q.2, hq, hqc⟩
    exact ⟨i, hzc ▸ hzq⟩

theorem incidence_cover (E : Set Plane) :
    G.incidenceCenters G.W E ⊆ D.exceptional ∪
      ⋃ i, (D.piece i).family.incidenceCenters (D.piece i).family.W E := by
  rintro z ⟨u, hu, he⟩
  rcases D.cover (z, u) hu with hb | ⟨i, q, hq, hqe⟩
  · exact Or.inl hb
  · apply Or.inr
    apply mem_iUnion.mpr
    have hzc : q.1 = z := ((D.piece i).keep_center q hq).symm.trans (congrArg Prod.fst hqe)
    have hqc : (D.piece i).family.curve q = G.curve (z, u) :=
      ((D.piece i).toAnalyticPiece.curve_eq q hq).trans (congrArg G.curve hqe)
    have hzq : q.1 ∈ (D.piece i).family.incidenceCenters (D.piece i).family.W E :=
      ⟨q.2, hq, by rwa [hqc]⟩
    exact ⟨i, hzc ▸ hzq⟩

theorem incidence_null_of_no_piece (inputs : P5Inputs)
    (hn : ∀ i, ¬ (D.piece i).family.AdmitsNikodym) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  intro E hE hE0
  apply measure_mono_null (D.incidence_cover E)
  apply measure_union_null D.null_exceptional
  apply measure_iUnion_null
  intro i
  exact constant_rank_incidence_null_of_noNikodym inputs (D.piece i).family
    (D.piece i).connected_domain.nonempty (D.piece i).open_domain (D.piece i).analytic_family
    (D.piece i).ranks (hn i) E hE hE0

theorem admitsNikodym_iff (inputs : P5Inputs) :
    G.AdmitsNikodym ↔ ∃ i, (D.piece i).family.AdmitsNikodym := by
  constructor
  · intro hG
    by_contra hn
    exact G.no_nikodym_of_incidence_null
      (D.incidence_null_of_no_piece inputs (fun i hi => hn ⟨i, hi⟩)) hG
  · rintro ⟨i, hi⟩
    exact (D.piece i).family.admitsNikodym_mono G (D.piece i).toAnalyticPiece.curves_mono hi

theorem hasMassiveCurveReuse_iff :
    G.HasMassiveCurveReuse ↔ ∃ i, (D.piece i).family.HasMassiveCurveReuse := by
  constructor
  · rintro ⟨β, hβ⟩
    obtain ⟨i, hi⟩ := hβ.exists_of_countable_cover
      (fun i => (D.piece i).family.centersOf β) (fun i => (D.piece i).centers_measurable β)
      (D.centers_cover β) D.null_exceptional
    exact ⟨i, β, hi⟩
  · rintro ⟨i, hi⟩
    exact (D.piece i).family.hasMassiveCurveReuse_mono G (D.piece i).toAnalyticPiece.curves_mono hi

include D in
theorem centers_nullMeasurable (β : Set Plane) : NullMeasurableSet (G.centersOf β) volume := by
  let S := ⋃ i, (D.piece i).family.centersOf β
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun i => (D.piece i).centers_measurable β)
  apply hS.nullMeasurableSet.congr
  filter_upwards [compl_mem_ae_iff.mpr D.null_exceptional] with z hz
  apply propext
  constructor
  · intro hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact (D.piece i).family.centersOf_mono G (D.piece i).toAnalyticPiece.curves_mono β hi
  · intro hg
    exact (D.centers_cover β hg).resolve_left hz

/-- Strong coverage of the reused curves in every piece covers every locally
reused original curve away from the CLOSED null centre exception. Finite
Borel centre fibres supply a positive H¹ witness in one piece. -/
theorem locallyReusedCovered_of_piece_strong (ha : G.IsAnalytic)
    (hstrong : ∀ i, (D.piece i).family.ReusedStronglyCovered) : G.LocallyReusedCovered := by
  classical
  choose V hV using hstrong
  let fields := Family.Foliations.finiteUnion V
  have hcover : ∀ p ∈ G.W, p.1 ∉ D.exceptional → G.LocallyReused p → G.Covered fields p := by
    intro p hp hpb hl
    let U : Set (Parameters 2 d) := Prod.fst ⁻¹' D.exceptionalᶜ
    have hU : U ∈ 𝓝 p :=
      (D.closed_exceptional.isOpen_compl.preimage continuous_fst).mem_nhds hpb
    have hpos := hl.2 U hU
    have hsub : Prod.fst '' (G.parametersOf (G.curve p) ∩ U) ⊆
        (∅ : Set (Base 2)) ∪ ⋃ i, (D.piece i).family.centersOf (G.curve p) := by
      rintro z ⟨q, ⟨⟨hq, hqc⟩, hqU⟩, hqz⟩
      have hz : z ∈ G.centersOf (G.curve p) := ⟨q, ⟨hq, hqc⟩, hqz⟩
      rcases D.centers_cover (G.curve p) hz with hb | hi
      · exact (hqU (hqz ▸ hb)).elim
      · exact Or.inr hi
    obtain ⟨i, hi⟩ := hpos.exists_of_countable_cover
      (fun i => (D.piece i).family.centersOf (G.curve p))
      (fun i => (D.piece i).centers_measurable (G.curve p)) hsub (measure_empty)
    obtain ⟨z, hz⟩ := hi.nonempty
    obtain ⟨u, hu, hc⟩ := ((D.piece i).family.mem_centersOf (G.curve p) z).mp hz
    have hcov := hV i (z, u) hu (hc.symm ▸ hi)
    have hcovG := G.covered_of_curve_eq (D.piece i).family ha.isSmooth p hp (z, u) (V i) hc.symm hcov
    exact G.covered_finiteUnion V i p hcovG
  refine ⟨fields, measure_mono_null ?_ D.null_exceptional⟩
  rintro z ⟨u, hl, hn⟩
  by_contra hb
  exact hn (hcover (z, u) hl.1 hb hl)

theorem locallyReusedCovered_of_negative (inputs : P5Inputs) (ha : G.IsAnalytic)
    (hm : ¬ G.HasMassiveCurveReuse) (hu : ∀ i, ¬ (D.piece i).family.LocalReuseNotCovered) :
    G.LocallyReusedCovered := by
  apply D.locallyReusedCovered_of_piece_strong ha
  intro i
  have hmi : ¬ (D.piece i).family.HasMassiveCurveReuse :=
    fun hi => hm ((D.hasMassiveCurveReuse_iff).mpr ⟨i, hi⟩)
  exact constant_rank_strong_cover_of_negative inputs (D.piece i).family
    (D.piece i).connected_domain.nonempty (D.piece i).open_domain (D.piece i).analytic_family
    (D.piece i).ranks hmi (hu i)

theorem localReuseNotCovered_iff (inputs : P5Inputs) (ha : G.IsAnalytic)
    (hm : ¬ G.HasMassiveCurveReuse) :
    G.LocalReuseNotCovered ↔ ∃ i, (D.piece i).family.LocalReuseNotCovered := by
  constructor
  · intro hG
    by_contra hn
    exact G.not_localReuseNotCovered_of_null_cover
      (D.locallyReusedCovered_of_negative inputs ha hm (fun i hi => hn ⟨i, hi⟩)) hG
  · rintro ⟨i, hi⟩
    exact (D.piece i).toAnalyticPiece.localReuseNotCovered_mono hi

/-- All four conclusions of Proposition 1.6, with the conditional premise
of its fourth conclusion preserved. Geometric metadata is in D.piece. -/
def Proposition16Conclusions : Prop :=
  (G.AdmitsNikodym ↔ ∃ i, (D.piece i).family.AdmitsNikodym) ∧
  (∀ i, ConstantRanks (D.piece i).family (D.piece i).point_rank (D.piece i).curve_rank) ∧
  (G.HasMassiveCurveReuse ↔ ∃ i, (D.piece i).family.HasMassiveCurveReuse) ∧
  (¬ G.HasMassiveCurveReuse →
    (G.LocalReuseNotCovered ↔ ∃ i, (D.piece i).family.LocalReuseNotCovered))

theorem proposition_1_6_of_decomposition (inputs : P5Inputs) (ha : G.IsAnalytic) :
    D.Proposition16Conclusions :=
  ⟨D.admitsNikodym_iff inputs, fun i => (D.piece i).ranks,
    D.hasMassiveCurveReuse_iff, D.localReuseNotCovered_iff inputs ha⟩

include D in
theorem classification (inputs : P5Inputs) (ha : G.IsAnalytic) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  constructor
  · intro hG
    obtain ⟨i, hi⟩ := (D.admitsNikodym_iff inputs).mp hG
    rcases (constant_rank_classification inputs (D.piece i).family
      (D.piece i).connected_domain.nonempty (D.piece i).open_domain (D.piece i).analytic_family
      (D.piece i).ranks).mp hi with hm | hu
    · exact Or.inl (D.hasMassiveCurveReuse_iff.mpr ⟨i, hm⟩)
    · exact Or.inr ((D.piece i).toAnalyticPiece.localReuseNotCovered_mono hu)
  · rintro (hm | hu)
    · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
    · by_cases hm : G.HasMassiveCurveReuse
      · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
      · obtain ⟨i, hi⟩ := (D.localReuseNotCovered_iff inputs ha hm).mp hu
        apply (D.admitsNikodym_iff inputs).mpr
        exact ⟨i, (constant_rank_classification inputs (D.piece i).family
          (D.piece i).connected_domain.nonempty (D.piece i).open_domain (D.piece i).analytic_family
          (D.piece i).ranks).mpr (Or.inr hi)⟩

include D in
theorem incidence_null_of_noNikodym (inputs : P5Inputs) (hn : ¬ G.AdmitsNikodym) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 :=
  D.incidence_null_of_no_piece inputs (fun i hi => hn ((D.admitsNikodym_iff inputs).mpr ⟨i, hi⟩))

include D in
theorem null_cover_of_noNikodym (inputs : P5Inputs) (ha : G.IsAnalytic) (hn : ¬ G.AdmitsNikodym) :
    G.LocallyReusedCovered := by
  apply D.locallyReusedCovered_of_negative inputs ha
  · exact fun hm => hn (G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm)
  · intro i hi
    apply hn
    apply (D.admitsNikodym_iff inputs).mpr
    exact ⟨i, (constant_rank_classification inputs (D.piece i).family
      (D.piece i).connected_domain.nonempty (D.piece i).open_domain (D.piece i).analytic_family
      (D.piece i).ranks).mpr (Or.inr hi)⟩

end RankDecomposition
end PlanarNikodym
