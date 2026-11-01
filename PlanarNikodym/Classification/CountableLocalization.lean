import PlanarNikodym.Classification.ReuseLocalization
import PlanarNikodym.Geometry.IncidenceCenters

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

structure OpenParameterCover {d : ℕ} (G : Family 2 d) where
  domain : ℕ → Set (Parameters 2 d)
  isOpen : ∀ i, IsOpen (domain i)
  subset : ∀ i, domain i ⊆ G.W
  covers : G.W ⊆ ⋃ i, domain i

namespace OpenParameterCover
variable {d : ℕ} {G : Family 2 d} (C : OpenParameterCover G)

abbrev family (i : ℕ) : Family 2 d := G.restrictTo (C.domain i)

theorem curves_mono (i : ℕ) (z : Base 2) :
    (C.family i).curvesAtOn (C.domain i) z ⊆ G.curvesAtOn G.W z := by
  rintro β ⟨u, hu, he⟩
  exact ⟨u, C.subset i hu, he⟩

theorem incidence_null (h : ∀ i, ∀ E, MeasurableSet E → volume E = 0 →
    volume ((C.family i).incidenceCenters (C.domain i) E) = 0) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  intro E hE hE0
  apply measure_mono_null (t := ⋃ i, (C.family i).incidenceCenters (C.domain i) E)
  · rintro z ⟨u, hu, hp⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (C.covers hu)
    exact mem_iUnion.mpr ⟨i, u, hi, hp⟩
  · exact measure_iUnion_null (fun i => h i E hE hE0)

theorem admitsNikodym_iff (h : ∀ i, ¬ (C.family i).AdmitsNikodym →
    ∀ E, MeasurableSet E → volume E = 0 →
      volume ((C.family i).incidenceCenters (C.domain i) E) = 0) :
    G.AdmitsNikodym ↔ ∃ i, (C.family i).AdmitsNikodym := by
  constructor
  · intro hG
    by_contra hn
    exact G.no_nikodym_of_incidence_null (C.incidence_null
      (fun i => h i (fun hi => hn ⟨i, hi⟩))) hG
  · rintro ⟨i, hi⟩
    exact (C.family i).admitsNikodym_mono G (C.curves_mono i) hi

theorem hasMassiveCurveReuse_iff
    (h : ∀ i β, NullMeasurableSet ((C.family i).centersOf β) volume) :
    G.HasMassiveCurveReuse ↔ ∃ i, (C.family i).HasMassiveCurveReuse := by
  constructor
  · rintro ⟨β, hp⟩
    have hcover : G.centersOf β ⊆ (∅ : Set (Base 2)) ∪ ⋃ i, (C.family i).centersOf β := by
      intro z hz
      obtain ⟨u, hu, hc⟩ := (G.mem_centersOf β z).mp hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp (C.covers hu)
      exact Or.inr (mem_iUnion.mpr ⟨i, ((C.family i).mem_centersOf β z).mpr ⟨u, hi, hc⟩⟩)
    obtain ⟨i, hi⟩ := hp.exists_of_countable_nullMeasurable_cover
      (fun i => (C.family i).centersOf β) (fun i => h i β) hcover measure_empty
    exact ⟨i, β, hi⟩
  · rintro ⟨i, hi⟩
    exact (C.family i).hasMassiveCurveReuse_mono G (C.curves_mono i) hi

/-- Outer-null local coverage certificates glue without assuming that
uncovered centre projections are Borel or that positive outer measure is
positive inner measure. -/
theorem locallyReusedCovered (h : ∀ i, (C.family i).LocallyReusedCovered) :
    G.LocallyReusedCovered := by
  classical
  choose V hV using h
  let fields := Family.Foliations.iUnion V
  refine ⟨fields, measure_mono_null ?_ (measure_iUnion_null hV)⟩
  rintro z ⟨u, hl, hn⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (C.covers hl.1)
  have hli := G.locallyReused_restrict_of_nhds (C.domain i) (z, u) ((C.isOpen i).mem_nhds hi) hl
  have hni : ¬ (C.family i).Covered (V i) (z, u) :=
    fun hc => hn (G.covered_iUnion V i (z, u) hc)
  exact mem_iUnion.mpr ⟨i, u, hli, hni⟩

theorem localReuseNotCovered_iff
    (h : ∀ i, ¬ (C.family i).LocalReuseNotCovered → (C.family i).LocallyReusedCovered) :
    G.LocalReuseNotCovered ↔ ∃ i, (C.family i).LocalReuseNotCovered := by
  constructor
  · intro hG
    by_contra hn
    exact G.not_localReuseNotCovered_of_null_cover
      (C.locallyReusedCovered (fun i => h i (fun hi => hn ⟨i, hi⟩))) hG
  · rintro ⟨i, hi⟩
    exact G.localReuseNotCovered_restrict_mono (C.domain i) (C.subset i) hi

end OpenParameterCover
end PlanarNikodym
