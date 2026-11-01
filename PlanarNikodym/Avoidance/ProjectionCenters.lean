import PlanarNikodym.Projection.ProjectionModel
import PlanarNikodym.Geometry.CoordinateMeasure
import PlanarNikodym.Geometry.AnalyticImplicit
import PlanarNikodym.Avoidance.AvoidanceMeasurability
import Mathlib.MeasureTheory.Measure.Regular

/-! A conull set of scalar-model parameters has a centre trace containing
a positive-measure compact set. The proof lifts the scalar projection to
a local analytic diffeomorphism, retaining all tail coordinates. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology ENNReal
namespace PlanarNikodym

def projectionConsEquiv (d : ℕ) : (ℝ × Aux d) ≃L[ℝ] Aux (d + 1) :=
  (Fin.consLinearEquiv ℝ (fun _ : Fin (d + 1) => ℝ)).toContinuousLinearEquiv

/-- Separate the two centre coordinates from the retained tail variables. -/
def projectionSplitEquiv (d : ℕ) : (ℝ × Aux (d + 1)) ≃L[ℝ] (Plane × Aux d) :=
  (show (ℝ × Aux (d + 1)) ≃ₗ[ℝ] (Plane × Aux d) from
    { toFun := fun p => ((p.1, p.2 0), Fin.tail p.2)
      invFun := fun p => (p.1.1, Fin.cons p.1.2 p.2)
      left_inv := by
        intro p
        refine Prod.ext (by rfl) ?_
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by intro p; rfl
      map_add' := by intro p q; rfl
      map_smul' := by intro r p; rfl }).toContinuousLinearEquiv

namespace ProjectionModel
variable {d : ℕ} (D : ProjectionModel d)

def centerMap (p : ℝ × Aux (d + 1)) : Plane := (p.1, D.κ p)

def centerLift (p : ℝ × Aux (d + 1)) : ℝ × Aux (d + 1) :=
  (p.1, Fin.cons (D.κ p) (Fin.tail p.2))

theorem centerLift_analytic : AnalyticOnNhd ℝ D.centerLift
    (ball D.base.1 D.radius ×ˢ ball D.base.2 D.radius) := by
  intro p hp
  have ht : AnalyticAt ℝ (fun p : ℝ × Aux (d + 1) => Fin.tail p.2) p := by
    apply AnalyticAt.pi
    intro i
    exact ((ContinuousLinearMap.proj i.succ : Aux (d + 1) →L[ℝ] ℝ).analyticAt _).comp analyticAt_snd
  exact analyticAt_fst.prod (((projectionConsEquiv d).analyticAt _).comp
    ((D.κ_analytic p hp).prod ht))

theorem centerLift_fderiv_invertible : (fderiv ℝ D.centerLift D.base).IsInvertible := by
  let E := ℝ × Aux (d + 1)
  let C := projectionConsEquiv d
  let T : Aux (d + 1) →L[ℝ] Aux d :=
    (ContinuousLinearMap.snd ℝ ℝ (Aux d)).comp C.symm.toContinuousLinearMap
  have hb : D.base ∈ ball D.base.1 D.radius ×ˢ ball D.base.2 D.radius :=
    ⟨mem_ball_self D.radius_pos, mem_ball_self D.radius_pos⟩
  have hk := (D.κ_analytic D.base hb).differentiableAt
  let A : E →L[ℝ] ℝ := fderiv ℝ D.κ D.base
  let P : E →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Aux (d + 1))
  let Q : E →L[ℝ] Aux (d + 1) := ContinuousLinearMap.snd ℝ ℝ (Aux (d + 1))
  let L : E →L[ℝ] E := P.prod (C.toContinuousLinearMap.comp (A.prod (T.comp Q)))
  have hL : HasFDerivAt D.centerLift L D.base :=
    hasFDerivAt_fst.prodMk
      (C.hasFDerivAt.comp D.base (hk.hasFDerivAt.prodMk (T.comp Q).hasFDerivAt))
  have hnorm : (fun w => D.κ (D.base.1, w)) =ᶠ[𝓝 D.base.2] (fun w : Aux (d + 1) => w 0) := by
    filter_upwards [ball_mem_nhds D.base.2 D.radius_pos] with w hw
    exact D.normalize w hw
  have hs : A.comp (ContinuousLinearMap.inr ℝ ℝ (Aux (d + 1))) = ContinuousLinearMap.proj 0 := by
    rw [← fderiv_snd_slice D.κ D.base hk, hnorm.fderiv_eq]
    exact (ContinuousLinearMap.proj 0 : Aux (d + 1) →L[ℝ] ℝ).fderiv
  have hz : ∀ v : E, L v = 0 → v = 0 := by
    intro v hv
    change (v.1, Fin.cons (A v) (Fin.tail v.2)) = 0 at hv
    have hx : v.1 = 0 := congrArg Prod.fst hv
    have hh : A v = 0 := by
      exact congrArg (fun p : E => p.2 0) hv
    have ht : Fin.tail v.2 = 0 := by
      exact congrArg (fun p : E => Fin.tail p.2) hv
    have hhead : v.2 0 = 0 := by
      have h := congrArg (fun M : Aux (d + 1) →L[ℝ] ℝ => M v.2) hs
      change A (0, v.2) = v.2 0 at h
      rw [← hx] at h
      exact h.symm.trans hh
    refine Prod.ext hx ?_
    ext i
    refine Fin.cases hhead (fun j => ?_) i
    exact congrFun ht j
  have hi : Injective L := by
    intro v w h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, h, sub_self]
  have hbL : Bijective L := ⟨hi, LinearMap.surjective_of_injective hi⟩
  rw [hL.fderiv]
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbL).toContinuousLinearEquiv, rfl⟩

/-- A planar null set remains null after adjoining any number of tail
coordinates, expressed in the scalar model's original coordinates. -/
theorem centerCoordinate_cylinder_null (A : Set Plane) (hA : volume A = 0) :
    volume {p : ℝ × Aux (d + 1) | (p.1, p.2 0) ∈ A} = 0 := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Aux d)) :=
    isAddHaarMeasure_volume_pi (Fin d)
  letI : Measure.IsAddHaarMeasure (volume : Measure (Aux (d + 1))) :=
    isAddHaarMeasure_volume_pi (Fin (d + 1))
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × Aux (d + 1))) := by
    change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure (Aux (d + 1))))
    infer_instance
  letI : Measure.IsAddHaarMeasure (volume : Measure (Plane × Aux d)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure Plane).prod (volume : Measure (Aux d)))
    infer_instance
  have hp : volume (A ×ˢ (univ : Set (Aux d))) = 0 := by
    change ((volume : Measure Plane).prod volume) _ = 0
    rw [Measure.prod_prod, hA, zero_mul]
  have hi := linearEquiv_image_null (projectionSplitEquiv d).symm volume volume _ hp
  apply measure_mono_null (t := (projectionSplitEquiv d).symm '' (A ×ˢ univ)) _ hi
  intro p hp
  exact ⟨projectionSplitEquiv d p, ⟨hp, mem_univ _⟩,
    (projectionSplitEquiv d).symm_apply_apply p⟩

/-- The centre trace of any conull measurable subset of the parameter ball
contains an actual positive-measure compact subset. -/
theorem centerTrace_hasPositivePart_of_conull (S : Set (Aux (d + 1)))
    (hS : MeasurableSet S) (_hSW : S ⊆ ball D.base.2 D.radius)
    (hS0 : volume (ball D.base.2 D.radius \ S) = 0) :
    HasPositivePart volume {c : Plane | ∃ x ∈ ball D.base.1 D.radius,
      ∃ w ∈ S, c = (x, D.κ (x, w))} := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Aux (d + 1))) :=
    isAddHaarMeasure_volume_pi (Fin (d + 1))
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × Aux (d + 1))) := by
    change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure (Aux (d + 1))))
    infer_instance
  let U := ball D.base.1 D.radius ×ˢ ball D.base.2 D.radius
  have hb : D.base ∈ U := ⟨mem_ball_self D.radius_pos, mem_ball_self D.radius_pos⟩
  obtain ⟨e, hbe, hes, he, hea, heia⟩ := exists_analytic_chart D.centerLift D.base
    (D.centerLift_analytic D.base hb) D.centerLift_fderiv_invertible U
      ((isOpen_ball.prod isOpen_ball).mem_nhds hb)
  let A : Set (ℝ × Aux (d + 1)) := e.source ∩ Prod.snd ⁻¹' S
  have hAm : MeasurableSet A := e.open_source.measurableSet.inter (hS.preimage measurable_snd)
  have hbad : volume ((univ : Set ℝ) ×ˢ (ball D.base.2 D.radius \ S)) = 0 := by
    change ((volume : Measure ℝ).prod volume) _ = 0
    rw [Measure.prod_prod, hS0, mul_zero]
  have hpos : 0 < volume A := by
    apply pos_iff_ne_zero.mpr
    intro hA0
    have hs : e.source ⊆ A ∪ ((univ : Set ℝ) ×ˢ (ball D.base.2 D.radius \ S)) := by
      intro p hp
      by_cases hw : p.2 ∈ S
      · exact Or.inl ⟨hp, hw⟩
      · exact Or.inr ⟨mem_univ _, (hes hp).2, hw⟩
    have hs0 := measure_mono_null hs (measure_union_null hA0 hbad)
    exact (e.open_source.measure_pos volume ⟨D.base, hbe⟩).ne' hs0
  obtain ⟨K, hKA, hKc, hKpos⟩ := hAm.exists_lt_isCompact hpos
  have hKU : K ⊆ U := fun p hp => hes (hKA hp).1
  have hc : ContinuousOn D.centerMap K :=
    continuousOn_fst.prodMk (D.κ_analytic.continuousOn.mono hKU)
  have hC : IsCompact (D.centerMap '' K) := hKc.image_of_continuousOn hc
  refine ⟨D.centerMap '' K, ?_, hC.measurableSet, ?_⟩
  · rintro c ⟨p, hp, rfl⟩
    exact ⟨p.1, (hKU hp).1, p.2, (hKA hp).2, rfl⟩
  · apply pos_iff_ne_zero.mpr
    intro hC0
    let Z : Set (ℝ × Aux (d + 1)) := {p | (p.1, p.2 0) ∈ D.centerMap '' K}
    have hZ0 : volume Z = 0 := centerCoordinate_cylinder_null (d := d) _ hC0
    have hpre0 := analytic_chart_preimage_null e heia volume Z hZ0
    have hsub : K ⊆ e.source ∩ e ⁻¹' Z := by
      intro p hp
      refine ⟨(hKA hp).1, ?_⟩
      change ((e p).1, (e p).2 0) ∈ D.centerMap '' K
      rw [he]
      exact ⟨p, hp, rfl⟩
    exact hKpos.ne' (measure_mono_null hsub hpre0)

theorem uncoveredTrace_hasPositivePart_of_timeCovered_null
    (V : Family.Foliations)
    (hnull : volume {w | w ∈ ball D.base.2 D.radius ∧ D.TimeCovered V w} = 0) :
    HasPositivePart volume (D.uncoveredTrace V) := by
  let S := {w | w ∈ ball D.base.2 D.radius ∧ ¬ D.TimeCovered V w}
  have hSW : S ⊆ ball D.base.2 D.radius := fun _ hw => hw.1
  have hS0 : volume (ball D.base.2 D.radius \ S) = 0 := by
    apply measure_mono_null (t := {w | w ∈ ball D.base.2 D.radius ∧ D.TimeCovered V w}) _ hnull
    intro w hw
    refine ⟨hw.1, ?_⟩
    by_contra hn
    exact hw.2 ⟨hw.1, hn⟩
  have hp := D.centerTrace_hasPositivePart_of_conull S (D.measurableSet_not_timeCovered V) hSW hS0
  apply hp.mono
  rintro c ⟨x, hx, w, hw, he⟩
  exact ⟨x, hx, w, hw.1, he, hw.2⟩

end ProjectionModel
end PlanarNikodym
