import PlanarNikodym.Avoidance.AvoidanceJets
import PlanarNikodym.Avoidance.AvoidanceMeasurability
import PlanarNikodym.Avoidance.RegularLevelNullity

/-! The noncritical-zero-set argument for §7.3, Step 3.
At a regular jet, the first two parameter covectors are independent.
Consequently tangency to one nonzero smooth field is a regular scalar
equation in the parameters, and hence has zero measure. -/

noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ENNReal
namespace PlanarNikodym.ProjectionModel

variable {d : ℕ} (D : ProjectionModel d)

def timeSlope (x : ℝ × Aux (d + 1)) : ℝ :=
  timeDerivative (fun y : ℝ × Aux (d + 1) => D.h y.1 y.2) 1 x

theorem timeSlope_eq_deriv (t : ℝ) (ht : t ∈ D.I.carrier)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    D.timeSlope (t, w) = deriv (fun s => D.h s w) t := by
  simpa only [timeSlope, iteratedDeriv_one] using
    timeDerivative_eq_iteratedDeriv 1 (t, w) (D.h_analytic (t, w) ⟨ht, hw⟩)

theorem timeSlope_analyticAt (t : ℝ) (ht : t ∈ D.I.carrier)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius) :
    AnalyticAt ℝ (fun w => D.timeSlope (t, w)) w :=
  (timeDerivative_analyticAt (D.h_analytic (t, w) ⟨ht, hw⟩) 1).comp
    (f := fun w : Aux (d + 1) => (t, w)) (analyticAt_const.prod analyticAt_id)

/-- At regular jets, the equation `h_t = A(h)` has nonzero parameter
derivative for every differentiable scalar function `A`. -/
theorem slope_residual_fderiv_ne_zero (hd : 0 < d) (t : ℝ) (ht : t ∈ D.I.carrier)
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius)
    (hdet : D.variationJetDet (t, w) ≠ 0) (A : ℝ → ℝ)
    (hA : DifferentiableAt ℝ A (D.h t w)) :
    fderiv ℝ (fun w => D.timeSlope (t, w) - A (D.h t w)) w ≠ 0 := by
  let j : Fin (d + 1) := ⟨1, by omega⟩
  let J := fderiv ℝ (D.timeJet t) w
  have hJ : Surjective J :=
    LinearMap.injective_iff_surjective.mp (D.timeJet_fderiv_injective t ht w hw hdet)
  obtain ⟨v, hv⟩ := hJ (Pi.single j 1)
  have h0 : fderiv ℝ (D.h t) w v = 0 := by
    have he := fderiv_apply (D.timeJet_analyticAt t ht w hw).differentiableAt
      (0 : Fin (d + 1))
    have hv0 : J v 0 = 0 := by simpa [j, Pi.single_apply] using congrFun hv 0
    change fderiv ℝ (fun w => D.timeJet t w 0) w v = 0
    rw [he]
    exact hv0
  have h1 : fderiv ℝ (fun w => D.timeSlope (t, w)) w v = 1 := by
    have he := fderiv_apply (D.timeJet_analyticAt t ht w hw).differentiableAt j
    have hv1 : J v j = 1 := by simpa using congrFun hv j
    change fderiv ℝ (fun w => D.timeJet t w j) w v = 1
    rw [he]
    exact hv1
  have hH : DifferentiableAt ℝ (D.h t) w :=
    ((D.h_analytic (t, w) ⟨ht, hw⟩).comp
      (f := fun w : Aux (d + 1) => (t, w)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hS := (D.timeSlope_analyticAt t ht w hw).differentiableAt
  intro hz
  have hzv := congrArg (fun L : Aux (d + 1) →L[ℝ] ℝ => L v) hz
  change (fderiv ℝ ((fun u => D.timeSlope (t, u)) - (A ∘ D.h t)) w) v = 0 at hzv
  rw [fderiv_sub hS (hA.comp w hH), fderiv_comp w hA hH] at hzv
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    h0, h1, map_zero, sub_zero] at hzv
  norm_num at hzv

/-- For a fixed time, regular tangencies to one smooth field form a null
set of parameters. -/
theorem regular_tangency_parameters_null (hd : 0 < d) (V : Family.Foliations)
    (i : ℕ) (t : ℝ) :
    volume {w | (t, w) ∈ D.tangencySet V i ∧ D.variationJetDet (t, w) ≠ 0} = 0 := by
  classical
  by_cases ht : t ∈ D.I.carrier
  · let B := ball D.base.2 D.radius
    let a : Aux (d + 1) → ℝ := B.piecewise (D.h t) (fun _ => 0)
    let b : Aux (d + 1) → ℝ := B.piecewise (fun w => D.timeSlope (t, w)) (fun _ => 0)
    let A : ℝ → ℝ := fun y => (V.field i (t, y)).2 / (V.field i (t, y)).1
    let f : Aux (d + 1) → ℝ := fun w => b w - A (a w)
    have ha : Measurable a :=
      (show ContinuousOn (D.h t) B from fun w hw =>
        (((D.h_analytic (t, w) ⟨ht, hw⟩).comp
          (f := fun w : Aux (d + 1) => (t, w))
          (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt)
      ).measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const isOpen_ball.measurableSet
    have hb : Measurable b :=
      (show ContinuousOn (fun w => D.timeSlope (t, w)) B from
        fun w hw => (D.timeSlope_analyticAt t ht w hw).continuousAt.continuousWithinAt
      ).measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const isOpen_ball.measurableSet
    have hV : Measurable (fun w : Aux (d + 1) => V.field i (t, a w)) :=
      (V.smooth i).continuous.measurable.comp (measurable_const.prodMk ha)
    have hf : Measurable f := hb.sub (hV.snd.div hV.fst)
    apply measure_mono_null (t := {w | f w = 0 ∧ fderiv ℝ f w ≠ 0})
    · intro w hw
      have hwB : w ∈ B := hw.1.1.2
      obtain ⟨hfirst, hslope⟩ := nonzero_tangent_iff_slope.mp hw.1.2
      have he : f =ᶠ[𝓝 w] fun v => D.timeSlope (t, v) - A (D.h t v) := by
        filter_upwards [isOpen_ball.mem_nhds hwB] with v hv
        simp only [f, a, b, piecewise_eq_of_mem B _ _ hv]
      refine ⟨?_, ?_⟩
      · rw [he.eq_of_nhds]
        rw [D.timeSlope_eq_deriv t ht w hwB]
        exact sub_eq_zero.mpr hslope
      · rw [he.fderiv_eq]
        apply D.slope_residual_fderiv_ne_zero hd t ht w hwB hw.2 A
        have hv : DifferentiableAt ℝ (fun y : ℝ => V.field i (t, y)) (D.h t w) :=
          ((V.smooth i).differentiable (by simp) (t, D.h t w)).comp (D.h t w)
            ((differentiableAt_const t).prodMk differentiableAt_id)
        exact hv.snd.div hv.fst hfirst
    · exact regular_zero_set_null f hf
  · have he : {w | (t, w) ∈ D.tangencySet V i ∧ D.variationJetDet (t, w) ≠ 0} = ∅ := by
      ext w
      simp only [mem_setOf_eq, tangencySet, timeParameterDomain, mem_prod, ht,
        false_and, mem_empty_iff_false]
    rw [he, measure_empty]

/-- A single nonzero smooth field is tangent only on a product-null set
of times and parameters. -/
theorem tangencySet_null (hd : 0 < d) (V : Family.Foliations) (i : ℕ) :
    (volume.prod volume) (D.tangencySet V i) = 0 := by
  let S := D.tangencySet V i \ D.variationJetDegenerateSet
  have hS : MeasurableSet S := (D.measurableSet_tangencySet V i).diff
    D.measurableSet_variationJetDegenerateSet
  have hnull : (volume.prod volume) S = 0 := by
    apply Measure.measure_prod_null_of_ae_null hS
    apply Filter.Eventually.of_forall
    intro t
    change volume (Prod.mk t ⁻¹' S) = 0
    apply measure_mono_null (t := {w | (t, w) ∈ D.tangencySet V i ∧
      D.variationJetDet (t, w) ≠ 0})
    · intro w hw
      refine ⟨hw.1, ?_⟩
      intro hz
      exact hw.2 ⟨hw.1.1, hz⟩
    · exact D.regular_tangency_parameters_null hd V i t
  apply measure_mono_null (t := S ∪ D.variationJetDegenerateSet)
  · intro x hx
    by_cases hdeg : x ∈ D.variationJetDegenerateSet
    · exact Or.inr hdeg
    · exact Or.inl ⟨hx, hdeg⟩
  · exact measure_union_null hnull D.variationJetDegenerateSet_null

/-- The countable field family is tangent for zero time measure at almost
every parameter. -/
theorem tangencyTimes_null_ae_parameters (hd : 0 < d) (V : Family.Foliations) :
    ∀ᵐ w ∂(volume : Measure (Aux (d + 1))), ∀ i,
      volume ((fun t : ℝ => (t, w)) ⁻¹' D.tangencySet V i) = 0 := by
  apply ae_all_iff.mpr
  intro i
  have hnull := D.tangencySet_null hd V i
  rw [Measure.prod_apply_symm (D.measurableSet_tangencySet V i),
    lintegral_eq_zero_iff (measurable_measure_prodMk_right
      (D.measurableSet_tangencySet V i))] at hnull
  exact hnull

/-- The principal avoidance statement before transporting parameters to
centre coordinates: almost no parameter is covered by the countable
smooth field family. -/
theorem timeCovered_parameters_null (hd : 0 < d) (V : Family.Foliations) :
    volume {w | w ∈ ball D.base.2 D.radius ∧ D.TimeCovered V w} = 0 := by
  have hnot : ∀ᵐ w ∂(volume : Measure (Aux (d + 1))),
      ¬(w ∈ ball D.base.2 D.radius ∧ D.TimeCovered V w) := by
    filter_upwards [D.tangencyTimes_null_ae_parameters hd V] with w hw hcov
    obtain ⟨i, hi⟩ := D.exists_tangencyTimes_pos_of_timeCovered V w hcov.1 hcov.2
    exact (ne_of_gt hi) (hw i)
  simpa only [not_not] using ae_iff.mp hnot

end PlanarNikodym.ProjectionModel
