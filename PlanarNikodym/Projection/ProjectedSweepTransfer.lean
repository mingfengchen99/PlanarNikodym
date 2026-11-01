import PlanarNikodym.Projection.StationaryConstructionTransfer
import PlanarNikodym.Core.AnalyticSetMeasurability

/-! The measurable sweep reduction in §7.3, Step 5.

A prescribed-projection construction must still provide the parameter
set with the required null and positive projections. The general result
below retains a general completed-measurable entry point. For Borel
parameter sets, completed measurability is proved using descriptive
analyticity; no Borel measurability of the image is asserted. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace PlanarNikodym

/-- The set swept out by the scalar projections indexed by `J`. -/
def scalarProjectionSweep {F : Type*} (φ : ℝ → F → ℝ)
    (J : Set ℝ) (G : Set F) : Set Plane :=
  {p | p.1 ∈ J ∧ p.2 ∈ φ p.1 '' G}

theorem scalarProjectionSweep_eq_image {F : Type*}
    (φ : ℝ → F → ℝ) (J : Set ℝ) (G : Set F) :
    scalarProjectionSweep φ J G = (fun p : ℝ × F => (p.1, φ p.1 p.2)) '' (J ×ˢ G) := by
  ext p
  constructor
  · rintro ⟨hp, w, hw, he⟩
    exact ⟨(p.1, w), ⟨hp, hw⟩, Prod.ext rfl he⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, q.2, hq.2, rfl⟩

/-- Images of Borel parameter sets are descriptive analytic sets. This
statement does not claim Borel measurability or completed measurability. -/
theorem scalarProjectionSweep_analyticSet {F : Type*}
    [TopologicalSpace F] [PolishSpace F] [MeasurableSpace F] [BorelSpace F]
    (φ : ℝ → F → ℝ) (J : Set ℝ) (G : Set F)
    (hJ : MeasurableSet J) (hG : MeasurableSet G)
    (hφ : ContinuousOn (fun p : ℝ × F => φ p.1 p.2) (J ×ˢ G)) :
    AnalyticSet (scalarProjectionSweep φ J G) := by
  rw [scalarProjectionSweep_eq_image]
  exact (hJ.prod hG).analyticSet.image_of_continuousOn (continuousOn_fst.prodMk hφ)

/-- The actual sweep of a Borel parameter set is measurable in the
Lebesgue completion, even when the projection image is not Borel. -/
theorem scalarProjectionSweep_nullMeasurableSet {F : Type*}
    [TopologicalSpace F] [PolishSpace F] [MeasurableSpace F] [BorelSpace F]
    (φ : ℝ → F → ℝ) (J : Set ℝ) (G : Set F)
    (hJ : MeasurableSet J) (hG : MeasurableSet G)
    (hφ : ContinuousOn (fun p : ℝ × F => φ p.1 p.2) (J ×ˢ G)) :
    NullMeasurableSet (scalarProjectionSweep φ J G) volume :=
  analyticSet_nullMeasurableSet (scalarProjectionSweep_analyticSet φ J G hJ hG hφ) volume

theorem scalarProjectionSweep_image {F Q : Type*}
    (φ : ℝ → F → ℝ) (ι : Q → F) (J : Set ℝ) (G : Set Q) :
    scalarProjectionSweep φ J (ι '' G) =
      scalarProjectionSweep (fun t q => φ t (ι q)) J G := by
  ext p
  simp only [scalarProjectionSweep, mem_setOf_eq, image_image]

/-- The section formula for a completed-measurable product set, obtained
from a Borel representative and the null-set form of Fubini. -/
theorem prod_apply_of_nullMeasurableSet {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    {S : Set (A × B)} (hS : NullMeasurableSet S (μ.prod ν)) :
    (μ.prod ν) S = ∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ := by
  obtain ⟨T, _, hT, hTS⟩ := hS.exists_measurable_superset_ae_eq
  have hsec : (fun x => ν (Prod.mk x ⁻¹' T)) =ᵐ[μ]
      (fun x => ν (Prod.mk x ⁻¹' S)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hTS] with x hx
    exact measure_congr hx
  calc
    (μ.prod ν) S = (μ.prod ν) T := (measure_congr hTS).symm
    _ = ∫⁻ x, ν (Prod.mk x ⁻¹' T) ∂μ := Measure.prod_apply hT
    _ = ∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ := lintegral_congr_ae hsec

/-- Section measures of a completed-measurable product set are almost
everywhere measurable, by comparison with a Borel representative. -/
theorem aemeasurable_sectionMeasure_of_nullMeasurableSet {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    {S : Set (A × B)} (hS : NullMeasurableSet S (μ.prod ν)) :
    AEMeasurable (fun x => ν (Prod.mk x ⁻¹' S)) μ := by
  obtain ⟨T, _, hT, hTS⟩ := hS.exists_measurable_superset_ae_eq
  apply (measurable_measure_prodMk_left (ν := ν) hT).aemeasurable.congr
  filter_upwards [Measure.ae_ae_of_ae_prod hTS] with x hx
  exact measure_congr hx

theorem aemeasurable_volume_scalarProjections {F : Type*}
    (φ : ℝ → F → ℝ) (J : Set ℝ) (G : Set F) (hJ : MeasurableSet J)
    (hm : NullMeasurableSet (scalarProjectionSweep φ J G) volume) :
    AEMeasurable (fun t => volume (φ t '' G)) (volume.restrict J) := by
  have hsec := aemeasurable_sectionMeasure_of_nullMeasurableSet volume volume hm
  apply hsec.restrict.congr
  filter_upwards [ae_restrict_mem hJ] with t ht
  have he : Prod.mk t ⁻¹' scalarProjectionSweep φ J G = φ t '' G := by
    ext y
    simp only [scalarProjectionSweep, mem_preimage, mem_setOf_eq, ht, true_and]
  exact congrArg volume he

/-- For actual completed-measurable sweeps, the zero integral appearing
in Proposition 4.2 is equivalent to almost every projection being null. -/
theorem lintegral_volume_scalarProjections_eq_zero_iff {F : Type*}
    (φ : ℝ → F → ℝ) (J : Set ℝ) (G : Set F) (hJ : MeasurableSet J)
    (hm : NullMeasurableSet (scalarProjectionSweep φ J G) volume) :
    (∫⁻ t in J, volume (φ t '' G)) = 0 ↔
      ∀ᵐ t ∂volume.restrict J, volume (φ t '' G) = 0 :=
  lintegral_eq_zero_iff' (aemeasurable_volume_scalarProjections φ J G hJ hm)

theorem scalarProjectionSweep_volume_eq_lintegral {F : Type*}
    (φ : ℝ → F → ℝ) (J : Set ℝ) (G : Set F)
    (hJ : MeasurableSet J)
    (hm : NullMeasurableSet (scalarProjectionSweep φ J G) volume) :
    volume (scalarProjectionSweep φ J G) = ∫⁻ x in J, volume (φ x '' G) := by
  change (volume.prod volume) (scalarProjectionSweep φ J G) = _
  rw [prod_apply_of_nullMeasurableSet volume volume hm, ← lintegral_indicator hJ]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ J
  · have he : Prod.mk x ⁻¹' scalarProjectionSweep φ J G = φ x '' G := by
      ext y
      simp only [scalarProjectionSweep, mem_preimage, mem_setOf_eq, hx, true_and]
    simp only [he, indicator_of_mem hx]
  · have he : Prod.mk x ⁻¹' scalarProjectionSweep φ J G = ∅ := by
      ext y
      simp only [scalarProjectionSweep, mem_preimage, mem_setOf_eq, hx, false_and,
        mem_empty_iff_false]
    simp only [he, measure_empty, indicator_of_notMem hx]

namespace ProjectionModel
variable {d : ℕ} (D : ProjectionModel d)

theorem curveSweep_analyticSet (J : Set ℝ) (G : Set (Aux (d + 1)))
    (hJ : MeasurableSet J) (hG : MeasurableSet G)
    (hJI : J ⊆ D.I.carrier) (hGB : G ⊆ Metric.ball D.base.2 D.radius) :
    AnalyticSet (scalarProjectionSweep D.h J G) := by
  apply scalarProjectionSweep_analyticSet D.h J G hJ hG
  exact D.h_analytic.continuousOn.mono (Set.prod_mono hJI hGB)

theorem centerSweep_analyticSet (X : Set ℝ) (G : Set (Aux (d + 1)))
    (hX : MeasurableSet X) (hG : MeasurableSet G)
    (hXB : X ⊆ Metric.ball D.base.1 D.radius)
    (hGB : G ⊆ Metric.ball D.base.2 D.radius) :
    AnalyticSet (scalarProjectionSweep (fun x w => D.κ (x, w)) X G) := by
  apply scalarProjectionSweep_analyticSet _ X G hX hG
  exact D.κ_analytic.continuousOn.mono (Set.prod_mono hXB hGB)

theorem curveSweep_nullMeasurableSet (J : Set ℝ) (G : Set (Aux (d + 1)))
    (hJ : MeasurableSet J) (hG : MeasurableSet G)
    (hJI : J ⊆ D.I.carrier) (hGB : G ⊆ Metric.ball D.base.2 D.radius) :
    NullMeasurableSet (scalarProjectionSweep D.h J G) volume :=
  analyticSet_nullMeasurableSet (D.curveSweep_analyticSet J G hJ hG hJI hGB) volume

theorem centerSweep_nullMeasurableSet (X : Set ℝ) (G : Set (Aux (d + 1)))
    (hX : MeasurableSet X) (hG : MeasurableSet G)
    (hXB : X ⊆ Metric.ball D.base.1 D.radius)
    (hGB : G ⊆ Metric.ball D.base.2 D.radius) :
    NullMeasurableSet (scalarProjectionSweep (fun x w => D.κ (x, w)) X G) volume :=
  analyticSet_nullMeasurableSet (D.centerSweep_analyticSet X G hX hG hXB hGB) volume

/-- Given the actual prescribed-projection witnesses, the sweep has a
Borel null envelope and its successful centre trace has positive inner
measure. The two completed-measurability hypotheses are explicit: they
are not inferred from the Borel nature of the parameter set. -/
theorem exists_null_set_of_projected_sweeps
    (J X : Set ℝ) (G : Set (Aux (d + 1)))
    (hJ : MeasurableSet J) (hX : MeasurableSet X)
    (hJI : J ⊆ D.I.carrier) (hJpos : 0 < volume J)
    (hXB : X ⊆ Metric.ball D.base.1 D.radius)
    (hGB : G ⊆ Metric.ball D.base.2 D.radius)
    (hmh : NullMeasurableSet (scalarProjectionSweep D.h J G) volume)
    (hmκ : NullMeasurableSet
      (scalarProjectionSweep (fun x w => D.κ (x, w)) X G) volume)
    (hnull : ∀ᵐ t ∂volume.restrict J, volume (D.h t '' G) = 0)
    (hpos : 0 < ∫⁻ x in X, volume ((fun w => D.κ (x, w)) '' G)) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) := by
  let S := scalarProjectionSweep D.h J G
  let E := toMeasurable volume S
  have hS0 : volume S = 0 := by
    rw [scalarProjectionSweep_volume_eq_lintegral D.h J G hJ hmh]
    exact lintegral_eq_zero_of_ae_eq_zero hnull
  have hE0 : volume E = 0 := (measure_toMeasurable S).trans hS0
  refine ⟨E, measurableSet_toMeasurable volume S, hE0, ?_⟩
  have hCpos : 0 < volume (scalarProjectionSweep (fun x w => D.κ (x, w)) X G) := by
    rwa [scalarProjectionSweep_volume_eq_lintegral _ X G hX hmκ]
  apply (HasPositivePart.of_nullMeasurable_pos hmκ hCpos).mono
  intro c hc
  obtain ⟨w, hw, he⟩ := hc.2
  refine ⟨c.1, hXB hc.1, w, hGB hw, Prod.ext rfl he.symm, ?_⟩
  have hJhit : J ⊆ D.hitTimes w E := by
    intro t ht
    refine ⟨hJI ht, subset_toMeasurable volume S ?_⟩
    exact ⟨ht, w, hw, rfl⟩
  exact lt_of_lt_of_le hJpos (measure_mono hJhit)

/-- The Borel version of the sweep transfer has no extra measurability
hypotheses on the projected sets. The zero and positive projection
properties still have to be proved for an actual selection set `G`. -/
theorem exists_null_set_of_borel_projected_sweeps
    (J X : Set ℝ) (G : Set (Aux (d + 1)))
    (hJ : MeasurableSet J) (hX : MeasurableSet X) (hG : MeasurableSet G)
    (hJI : J ⊆ D.I.carrier) (hJpos : 0 < volume J)
    (hXB : X ⊆ Metric.ball D.base.1 D.radius)
    (hGB : G ⊆ Metric.ball D.base.2 D.radius)
    (hnull : ∀ᵐ t ∂volume.restrict J, volume (D.h t '' G) = 0)
    (hpos : 0 < ∫⁻ x in X, volume ((fun w => D.κ (x, w)) '' G)) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) :=
  D.exists_null_set_of_projected_sweeps J X G hJ hX hJI hJpos hXB hGB
    (D.curveSweep_nullMeasurableSet J G hJ hG hJI hGB)
    (D.centerSweep_nullMeasurableSet X G hX hG hXB hGB) hnull hpos

/-- A Borel selection can be made in any Polish parameter space and
inserted continuously into the original auxiliary space. In particular,
the selection in Proposition 4.2 is made in a two-dimensional slice. -/
theorem exists_null_set_of_parameterized_projected_sweeps {Q : Type*}
    [TopologicalSpace Q] [PolishSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (ι : Q → Aux (d + 1)) (hι : Continuous ι)
    (J X : Set ℝ) (G : Set Q)
    (hJ : MeasurableSet J) (hX : MeasurableSet X) (hG : MeasurableSet G)
    (hJI : J ⊆ D.I.carrier) (hJpos : 0 < volume J)
    (hXB : X ⊆ Metric.ball D.base.1 D.radius)
    (hGB : ∀ q ∈ G, ι q ∈ Metric.ball D.base.2 D.radius)
    (hnull : ∀ᵐ t ∂volume.restrict J, volume ((fun q => D.h t (ι q)) '' G) = 0)
    (hpos : 0 < ∫⁻ x in X, volume ((fun q => D.κ (x, ι q)) '' G)) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) := by
  apply D.exists_null_set_of_projected_sweeps J X (ι '' G) hJ hX hJI hJpos hXB
    (by rintro _ ⟨q, hq, rfl⟩; exact hGB q hq)
  · rw [scalarProjectionSweep_image]
    apply scalarProjectionSweep_nullMeasurableSet _ J G hJ hG
    exact D.h_analytic.continuousOn.comp
      (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hJI hp.1, hGB p.2 hp.2⟩)
  · rw [scalarProjectionSweep_image]
    apply scalarProjectionSweep_nullMeasurableSet _ X G hX hG
    exact D.κ_analytic.continuousOn.comp
      (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hXB hp.1, hGB p.2 hp.2⟩)
  · simpa only [image_image] using hnull
  · simpa only [image_image] using hpos

/-- The concrete two-slice transfer used after the nonstationary
prescribed-projection construction. Both sweeps are proved measurable
in the completion, and the centre conclusion is positive inner measure. -/
theorem exists_null_set_of_twoSlice_projected_sweeps
    (j : Fin (d + 1)) (J X : Set ℝ) (G : Set Plane)
    (hJ : MeasurableSet J) (hX : MeasurableSet X) (hG : MeasurableSet G)
    (hJI : J ⊆ D.I.carrier) (hJpos : 0 < volume J)
    (hXB : X ⊆ Metric.ball D.base.1 D.radius)
    (hGB : ∀ q ∈ G, twoParameterInsert D.base.2 j q ∈ Metric.ball D.base.2 D.radius)
    (hnull : ∀ᵐ t ∂volume.restrict J, volume ((fun q => D.twoSliceCurves j (t, q)) '' G) = 0)
    (hpos : 0 < ∫⁻ x in X, volume ((fun q => D.twoSliceCenters j (x, q)) '' G)) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) :=
  D.exists_null_set_of_parameterized_projected_sweeps (twoParameterInsert D.base.2 j)
    (continuousOn_univ.mp
      (twoParameterInsert_analytic D.base.2 j).continuousOn)
    J X G hJ hX hG hJI hJpos hXB hGB hnull hpos

/-- Direct exit for the two projection integrals in Proposition 4.2.
All measurability needed to turn the null integral into almost-everywhere
null projections, and then into a Borel null envelope, is proved here. -/
theorem exists_null_set_of_twoSlice_projection_integrals
    (j : Fin (d + 1)) (J X : Set ℝ) (G : Set Plane)
    (hJ : MeasurableSet J) (hX : MeasurableSet X) (hG : MeasurableSet G)
    (hJI : J ⊆ D.I.carrier) (hJpos : 0 < volume J)
    (hXB : X ⊆ Metric.ball D.base.1 D.radius)
    (hGB : ∀ q ∈ G, twoParameterInsert D.base.2 j q ∈ Metric.ball D.base.2 D.radius)
    (hnull : (∫⁻ t in J, volume ((fun q => D.twoSliceCurves j (t, q)) '' G)) = 0)
    (hpos : 0 < ∫⁻ x in X, volume ((fun q => D.twoSliceCenters j (x, q)) '' G)) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) := by
  have hm : NullMeasurableSet
      (scalarProjectionSweep (fun t q => D.twoSliceCurves j (t, q)) J G) volume := by
    apply scalarProjectionSweep_nullMeasurableSet _ J G hJ hG
    exact fun p hp => (D.twoSliceCurves_analyticAt j p (hJI hp.1)
      (hGB p.2 hp.2)).continuousAt.continuousWithinAt
  exact D.exists_null_set_of_twoSlice_projected_sweeps j J X G hJ hX hG hJI hJpos hXB hGB
    ((lintegral_volume_scalarProjections_eq_zero_iff _ J G hJ hm).mp hnull) hpos

end ProjectionModel
end PlanarNikodym
