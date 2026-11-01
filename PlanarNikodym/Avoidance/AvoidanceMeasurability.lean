import PlanarNikodym.Projection.ProjectionModel
import PlanarNikodym.Geometry.Cinematic
import Mathlib.MeasureTheory.Measure.Prod

/-! Borel measurability of the time/parameter predicates in §7.3.
Only the prescribed analytic neighbourhood is used; no global regularity
of the ambient extension `h` is assumed. -/

noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
namespace PlanarNikodym.ProjectionModel

variable {d : ℕ} (D : ProjectionModel d)

/-- A nonzero field tangent to a graph has nonzero time component, so the
tangency condition is the ordinary scalar ODE for its normalized slope. -/
theorem nonzero_tangent_iff_slope {v : Plane} {s : ℝ} :
    (v ≠ 0 ∧ Family.wedge v (1, s) = 0) ↔
      v.1 ≠ 0 ∧ s = v.2 / v.1 := by
  constructor
  · rintro ⟨hv, ht⟩
    have hfst : v.1 ≠ 0 := by
      intro hz
      apply hv
      apply Prod.ext hz
      change v.2 = 0
      dsimp [Family.wedge] at ht
      simpa only [hz, zero_mul, mul_one, zero_sub, neg_eq_zero] using ht
    refine ⟨hfst, (eq_div_iff hfst).mpr ?_⟩
    dsimp [Family.wedge] at ht
    nlinarith
  · rintro ⟨hfst, hs⟩
    constructor
    · intro hz
      exact hfst (congrArg Prod.fst hz)
    · have hm := (eq_div_iff hfst).mp hs
      dsimp [Family.wedge]
      nlinarith

theorem timeCovered_iff_slope (V : Family.Foliations) (w : Aux (d + 1)) :
    D.TimeCovered V w ↔
      ∀ᵐ t ∂volume.restrict D.I.carrier, ∃ i,
        (V.field i (t, D.h t w)).1 ≠ 0 ∧
          deriv (fun s => D.h s w) t =
            (V.field i (t, D.h t w)).2 / (V.field i (t, D.h t w)).1 := by
  simp only [TimeCovered, nonzero_tangent_iff_slope]

def timeParameterDomain : Set (ℝ × Aux (d + 1)) :=
  D.I.carrier ×ˢ Metric.ball D.base.2 D.radius

theorem measurableSet_timeParameterDomain : MeasurableSet D.timeParameterDomain :=
  measurableSet_Icc.prod Metric.isOpen_ball.measurableSet

/-- Tangencies to one field, expressed with the genuine time derivative. -/
def tangencySet (V : Family.Foliations) (i : ℕ) : Set (ℝ × Aux (d + 1)) :=
  {x | x ∈ D.timeParameterDomain ∧
    V.field i (x.1, D.h x.1 x.2) ≠ 0 ∧
      Family.wedge (V.field i (x.1, D.h x.1 x.2))
        (1, deriv (fun t => D.h t x.2) x.1) = 0}

theorem measurableSet_tangencySet (V : Family.Foliations) (i : ℕ) :
    MeasurableSet (D.tangencySet V i) := by
  classical
  let H : ℝ × Aux (d + 1) → ℝ := fun x => D.h x.1 x.2
  let a : ℝ × Aux (d + 1) → ℝ := D.timeParameterDomain.piecewise H (fun _ => 0)
  let b : ℝ × Aux (d + 1) → ℝ :=
    D.timeParameterDomain.piecewise (timeDerivative H 1) (fun _ => 0)
  have ha : Measurable a :=
    (show ContinuousOn H D.timeParameterDomain from D.h_analytic.continuousOn
    ).measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
      D.measurableSet_timeParameterDomain
  have hb : Measurable b :=
    (show ContinuousOn (timeDerivative H 1) D.timeParameterDomain from
      fun x hx => (timeDerivative_analyticAt (D.h_analytic x hx) 1).continuousAt.continuousWithinAt
    ).measurable_piecewise continuousOn_const D.measurableSet_timeParameterDomain
  have hv : Measurable (fun x : ℝ × Aux (d + 1) => V.field i (x.1, a x)) :=
    (V.smooth i).continuous.measurable.comp (measurable_fst.prodMk ha)
  have hw : Measurable (fun x : ℝ × Aux (d + 1) =>
      Family.wedge (V.field i (x.1, a x)) (1, b x)) := by
    exact (hv.fst.mul hb).sub (hv.snd.mul measurable_const)
  have hm : MeasurableSet {x : ℝ × Aux (d + 1) | x ∈ D.timeParameterDomain ∧
      V.field i (x.1, a x) ≠ 0 ∧
        Family.wedge (V.field i (x.1, a x)) (1, b x) = 0} :=
    D.measurableSet_timeParameterDomain.inter
      ((measurableSet_eq_fun hv measurable_const).compl.inter
        (measurableSet_eq_fun hw measurable_const))
  convert hm using 1
  ext x
  by_cases hx : x ∈ D.timeParameterDomain
  · have he : timeDerivative H 1 x = deriv (fun t => D.h t x.2) x.1 := by
      simpa only [iteratedDeriv_one] using
        timeDerivative_eq_iteratedDeriv 1 x (D.h_analytic x hx)
    simp only [tangencySet, mem_setOf_eq, hx, true_and,
      a, b, piecewise_eq_of_mem D.timeParameterDomain _ _ hx, H, he]
  · simp only [tangencySet, mem_setOf_eq, hx, false_and]

theorem measurableSet_tangencyTimes (V : Family.Foliations) (i : ℕ)
    (w : Aux (d + 1)) :
    MeasurableSet ((fun t : ℝ => (t, w)) ⁻¹' D.tangencySet V i) :=
  (D.measurableSet_tangencySet V i).preimage (measurable_id.prodMk measurable_const)

/-- The points at which none of the countably many nonzero fields is tangent. -/
def uncoveredTimeSet (V : Family.Foliations) : Set (ℝ × Aux (d + 1)) :=
  D.timeParameterDomain \ ⋃ i, D.tangencySet V i

theorem measurableSet_uncoveredTimeSet (V : Family.Foliations) :
    MeasurableSet (D.uncoveredTimeSet V) :=
  D.measurableSet_timeParameterDomain.diff
    (MeasurableSet.iUnion (D.measurableSet_tangencySet V))

/-- A Borel function of the parameters. Its positivity detects failure of
almost-everywhere coverage for parameters in the model ball. -/
def uncoveredTimeMass (V : Family.Foliations) (w : Aux (d + 1)) : ℝ≥0∞ :=
  volume ((fun t : ℝ => (t, w)) ⁻¹' D.uncoveredTimeSet V)

theorem measurable_uncoveredTimeMass (V : Family.Foliations) :
    Measurable (D.uncoveredTimeMass V) :=
  measurable_measure_prodMk_right (D.measurableSet_uncoveredTimeSet V)

theorem timeCovered_iff_uncoveredTimeMass_eq_zero (V : Family.Foliations)
    (w : Aux (d + 1)) (hw : w ∈ Metric.ball D.base.2 D.radius) :
    D.TimeCovered V w ↔ D.uncoveredTimeMass V w = 0 := by
  rw [TimeCovered, ae_restrict_iff' (show MeasurableSet D.I.carrier from measurableSet_Icc), ae_iff]
  change volume {t | ¬(t ∈ D.I.carrier → ∃ i,
    V.field i (t, D.h t w) ≠ 0 ∧
      Family.wedge (V.field i (t, D.h t w))
        (1, deriv (fun s => D.h s w) t) = 0)} = 0 ↔ _
  have he : {t | ¬(t ∈ D.I.carrier → ∃ i,
      V.field i (t, D.h t w) ≠ 0 ∧
        Family.wedge (V.field i (t, D.h t w))
          (1, deriv (fun s => D.h s w) t) = 0)} =
      (fun t : ℝ => (t, w)) ⁻¹' D.uncoveredTimeSet V := by
    ext t
    have hwdist := Metric.mem_ball.mp hw
    by_cases ht : t ∈ D.I.carrier <;>
      simp [uncoveredTimeSet, tangencySet, timeParameterDomain, ht, hw, hwdist]
  simp only [uncoveredTimeMass, he]

theorem not_timeCovered_iff_uncoveredTimeMass_pos (V : Family.Foliations)
    (w : Aux (d + 1)) (hw : w ∈ Metric.ball D.base.2 D.radius) :
    ¬ D.TimeCovered V w ↔ 0 < D.uncoveredTimeMass V w := by
  rw [D.timeCovered_iff_uncoveredTimeMass_eq_zero V w hw, pos_iff_ne_zero]

/-- Countability reduces a covered curve to one field tangent on a set of
positive time measure. No measurability of a centre projection is used. -/
theorem exists_tangencyTimes_pos_of_timeCovered (V : Family.Foliations)
    (w : Aux (d + 1)) (hw : w ∈ Metric.ball D.base.2 D.radius)
    (hcovered : D.TimeCovered V w) :
    ∃ i, 0 < volume ((fun t : ℝ => (t, w)) ⁻¹' D.tangencySet V i) := by
  by_contra! hnone
  have hz : volume (⋃ i, (fun t : ℝ => (t, w)) ⁻¹' D.tangencySet V i) = 0 :=
    measure_iUnion_null (fun i => nonpos_iff_eq_zero.mp (hnone i))
  have hu : volume ((fun t : ℝ => (t, w)) ⁻¹' D.uncoveredTimeSet V) = 0 :=
    (D.timeCovered_iff_uncoveredTimeMass_eq_zero V w hw).mp hcovered
  have hsub : D.I.carrier ⊆
      (⋃ i, (fun t : ℝ => (t, w)) ⁻¹' D.tangencySet V i) ∪
        ((fun t : ℝ => (t, w)) ⁻¹' D.uncoveredTimeSet V) := by
    intro t ht
    by_cases hc : ∃ i, (t, w) ∈ D.tangencySet V i
    · exact Or.inl (mem_iUnion.mpr hc)
    · right
      exact ⟨⟨ht, hw⟩, by simpa only [mem_iUnion] using hc⟩
  have hnull : volume D.I.carrier = 0 :=
    measure_mono_null hsub (measure_union_null hz hu)
  have hpos : 0 < volume D.I.carrier := by
    rw [Interval.carrier, Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr D.I.nondegenerate)
  exact (ne_of_gt hpos) hnull

/-- The covered parameter set is Borel, even though its centre image need
not be Borel. -/
theorem measurableSet_timeCovered (V : Family.Foliations) :
    MeasurableSet {w | w ∈ Metric.ball D.base.2 D.radius ∧ D.TimeCovered V w} := by
  have he : {w | w ∈ Metric.ball D.base.2 D.radius ∧ D.TimeCovered V w} =
      Metric.ball D.base.2 D.radius ∩ {w | D.uncoveredTimeMass V w = 0} := by
    ext w
    by_cases hw : w ∈ Metric.ball D.base.2 D.radius
    · simp only [mem_setOf_eq, mem_inter_iff, hw, true_and,
        D.timeCovered_iff_uncoveredTimeMass_eq_zero V w hw]
    · simp only [mem_setOf_eq, mem_inter_iff, hw, false_and]
  rw [he]
  exact Metric.isOpen_ball.measurableSet.inter
    (measurableSet_eq_fun (D.measurable_uncoveredTimeMass V) measurable_const)

theorem measurableSet_not_timeCovered (V : Family.Foliations) :
    MeasurableSet {w | w ∈ Metric.ball D.base.2 D.radius ∧ ¬ D.TimeCovered V w} := by
  have he : {w | w ∈ Metric.ball D.base.2 D.radius ∧ ¬ D.TimeCovered V w} =
      Metric.ball D.base.2 D.radius \ {w | w ∈ Metric.ball D.base.2 D.radius ∧
        D.TimeCovered V w} := by
    ext w
    simp only [mem_setOf_eq, Set.mem_sdiff]
    tauto
  rw [he]
  exact Metric.isOpen_ball.measurableSet.diff (D.measurableSet_timeCovered V)

end PlanarNikodym.ProjectionModel
