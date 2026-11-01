import PlanarNikodym.Classification.Lemma71
import PlanarNikodym.Geometry.NullGeometry
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem measurableSet_inter_preimage_continuousOn {E F : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] [Zero F]
    (S : Set E) (hS : MeasurableSet S) (f : E → F) (hf : ContinuousOn f S)
    (A : Set F) (hA : MeasurableSet A) : MeasurableSet (S ∩ f ⁻¹' A) := by
  classical
  have hm : Measurable (S.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hS
  have he : S ∩ f ⁻¹' A = S ∩ (S.piecewise f (fun _ => 0)) ⁻¹' A := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [he]
  exact hS.inter (hm hA)

/-- Fubini and analytic local inverses give null pullback for a one-parameter
graph family. The exceptional critical locus is proved null, not assumed null. -/
theorem one_parameter_graph_preimage_null (I : Interval) (J : Set ℝ) (hJ : MeasurableSet J)
    (h : Plane → ℝ) (ha : AnalyticOnNhd ℝ h (I.carrier ×ˢ J))
    (hn : ∀ s ∈ J, ∃ t ∈ I.carrier, partialParameter h (t, s) ≠ 0)
    (E : Set Plane) (_hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume {p : Plane | p ∈ I.carrier ×ˢ J ∧ (p.1, h p) ∈ E} = 0 := by
  let S := I.carrier ×ˢ J
  let B := {p : Plane | p ∈ S ∧ partialParameter h p = 0}
  let G : Plane → Plane := fun p => (p.1, h p)
  have hS : MeasurableSet S := measurableSet_Icc.prod hJ
  have hD : AnalyticOnNhd ℝ (partialParameter h) S :=
    fun p hp => analyticAt_partialParameter (ha p hp)
  have hB : MeasurableSet B := by
    exact measurableSet_inter_preimage_continuousOn S hS _ hD.continuousOn {0}
      (measurableSet_singleton 0)
  have hB0 : volume B = 0 := by
    change (volume.prod volume) B = 0
    rw [Measure.prod_apply_symm hB]
    have hfibre : ∀ s : ℝ, volume ((fun t => (t, s)) ⁻¹' B) = 0 := by
      intro s
      by_cases hs : s ∈ J
      · have he : ((fun t => (t, s)) ⁻¹' B) =
            {t | t ∈ I.carrier ∧ partialParameter h (t, s) = 0} := by
          ext t; simp only [B, S, mem_preimage, mem_setOf_eq, mem_prod, hs, and_true]
        rw [he]
        exact analytic_zeros_null_interval I _ (fun t ht =>
          (hD (t, s) ⟨ht, hs⟩).comp (f := fun t : ℝ => (t, s))
            (analyticAt_id.prod analyticAt_const)) (hn s hs)
      · have he : ((fun t => (t, s)) ⁻¹' B) = ∅ := by
          ext t; simp [B, S, hs]
        rw [he, measure_empty]
    simp_rw [hfibre]
    simp
  have hG : AnalyticOnNhd ℝ G S := fun p hp => analyticAt_fst.prod (ha p hp)
  have hregular := analytic_regular_preimage_null G S hG volume E hE0
  apply measure_mono_null (t := B ∪ {p | p ∈ S ∧ (fderiv ℝ G p).IsInvertible ∧ G p ∈ E})
  · rintro p ⟨hp, he⟩
    by_cases hd : partialParameter h p = 0
    · exact Or.inl ⟨hp, hd⟩
    · refine Or.inr ⟨hp, ?_, he⟩
      have hder : fderiv ℝ G p =
          (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ h p) :=
        (hasFDerivAt_fst.prodMk (ha p hp).differentiableAt.hasFDerivAt).fderiv
      rw [hder]
      exact graph_derivative_invertible _ hd
  · exact measure_union_null hB0 hregular

theorem one_parameter_bad_parameters_null (I : Interval) (J : Set ℝ) (hJ : MeasurableSet J)
    (h : Plane → ℝ) (ha : AnalyticOnNhd ℝ h (I.carrier ×ˢ J))
    (hn : ∀ s ∈ J, ∃ t ∈ I.carrier, partialParameter h (t, s) ≠ 0)
    (E : Set Plane) (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume {s | s ∈ J ∧ 0 < volume {t | t ∈ I.carrier ∧ (t, h (t, s)) ∈ E}} = 0 := by
  let A := {p : Plane | p ∈ I.carrier ×ˢ J ∧ (p.1, h p) ∈ E}
  have hAm : MeasurableSet A :=
    measurableSet_inter_preimage_continuousOn _ (measurableSet_Icc.prod hJ)
      (fun p : Plane => (p.1, h p)) (continuousOn_fst.prodMk ha.continuousOn) E hE
  have hA0 := one_parameter_graph_preimage_null I J hJ h ha hn E hE hE0
  change (volume.prod volume) A = 0 at hA0
  rw [Measure.prod_apply_symm hAm] at hA0
  have hsections := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hAm)).mp hA0
  apply measure_mono_null (t := {s | volume ((fun t => (t, s)) ⁻¹' A) ≠ 0})
  · rintro s ⟨hs, hp⟩ hf
    have he : ((fun t => (t, s)) ⁻¹' A) =
        {t | t ∈ I.carrier ∧ (t, h (t, s)) ∈ E} := by
      ext t
      simp only [A, mem_preimage, mem_setOf_eq, mem_prod, hs, and_true]
    rw [he] at hf
    exact hp.ne' hf
  · exact ae_iff.mp hsections

end PlanarNikodym
