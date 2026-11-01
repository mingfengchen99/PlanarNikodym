import PlanarNikodym.Geometry.Cinematic
import PlanarNikodym.Classification.TimeLocalization

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- The outer-null version of Corollary 1.2 needed by the classification.
The cinematic determinant consists of actual mixed derivatives. This remains
an explicit analysis input for P7–P8; no proof is postulated as an axiom. -/
def CinematicNullInput : Prop :=
  ∀ (d : ℕ) (G : Family 2 d), IsOpen G.W → G.IsAnalytic →
    (∀ t ∈ G.I.carrier, ∀ p ∈ G.W, G.cinematicDet (t, p) ≠ 0) →
    ∀ E : Set Plane, MeasurableSet E → volume E = 0 →
      volume (G.timeIncidenceCenters G.W E) = 0

theorem Family.incidence_null_of_local {d : ℕ} (G : Family 2 d)
    (h : ∀ q ∈ G.W, ∃ U : Set (Parameters 2 d), IsOpen U ∧ q ∈ U ∧
      ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters U E) = 0) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  classical
  choose U hU using h
  obtain ⟨T, hTc, hT⟩ := (HereditarilyLindelofSpace.isLindelof G.W).elim_countable_subcover
    (fun q : G.W => U q q.property) (fun q => (hU q q.property).1) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, (hU p hp).2.1⟩)
  haveI := hTc.to_subtype
  intro E hE hE0
  apply measure_mono_null (t := ⋃ q : T, G.incidenceCenters (U q.val q.val.property) E)
  · rintro z ⟨u, hu, hp⟩
    obtain ⟨q, hq, hmem⟩ := mem_iUnion₂.mp (hT hu)
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, u, hmem, hp⟩
  · exact measure_iUnion_null (fun q => (hU q.val q.val.property).2.2 E hE hE0)

theorem full_curve_rank_incidence_null (hB : BocherInput) (hC : CinematicNullInput)
    {d : ℕ} (G : Family 2 d) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hc : ∀ p ∈ G.W, G.curveRank p = d + 2)
    (E : Set Plane) (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.incidenceCenters G.W E) = 0 := by
  rw [← G.timeIncidenceCenters_eq ha.isSmooth G.W Subset.rfl E]
  apply time_incidence_null_of_regular_patches G hW G.cinematicDet
    (G.cinematicDet_analytic ha).continuousOn
    (fun p hp => full_curve_rank_cinematic_exceptions_finite hB G ha p hp (hc p hp)) E
  intro J hJ U hU hUW hn
  let H := (G.withInterval J).restrictTo U
  have hHa : H.IsAnalytic := fun x hx => ha x ⟨hJ hx.1, hUW hx.2⟩
  exact hC d H hU hHa hn E hE hE0

theorem maximal_gap_incidence_null (hB : BocherInput) (hC : CinematicNullInput)
    {d m : ℕ} (G : Family 2 d) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G m (m + 2)) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  apply G.incidence_null_of_local
  intro q hq
  obtain ⟨U, hUo, hqU, _, Wz, Wu, H, hzO, huO, _, _, _, hprod, hHa, hHr, he⟩ :=
    corollary_6_2 G hW ha (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2) q hq
  refine ⟨U, hUo, hqU, ?_⟩
  intro E hE hE0
  exact measure_mono_null (G.incidenceCenters_mono H U H.W (fun z => (he z).subset) E)
    (full_curve_rank_incidence_null hB hC H (hprod ▸ hzO.prod huO) hHa
      (fun p hp => (hHr p hp).2) E hE hE0)

/-- The maximal rank-gap branch of Theorem 1.5. Nikodym exclusion depends
exactly on the two displayed external inputs. The no-reuse clause is proved
unconditionally by `maximal_gap_not_reused`. -/
theorem theorem_1_5_case_maximal_gap (hB : BocherInput) (hC : CinematicNullInput)
    {d m : ℕ} (G : Family 2 d) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G m (m + 2)) :
    ¬ G.AdmitsNikodym ∧ ∀ p ∈ G.W, ¬ G.Reused (G.curve p) :=
  ⟨G.no_nikodym_of_incidence_null (maximal_gap_incidence_null hB hC G hW ha hr),
    fun p _ => maximal_gap_not_reused G hW ha hr (G.curve p)⟩

end PlanarNikodym
