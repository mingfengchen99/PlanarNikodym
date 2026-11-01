import PlanarNikodym.Cells.AnalyticPieces
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! A genuine closure-nullity result for compactified lower-dimensional
centre charts. Compactness controls the closure; Hausdorff dimension
controls measure. No null-set assumption is made about the image. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace PlanarNikodym

/-- A smooth image of a compact set of dimension smaller than the target
dimension is a closed null set. The map need only be smooth on a convex
neighbourhood containing that compact set. -/
theorem compact_smooth_image_closed_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {f : E → Base n} {U K : Set E}
    (hf : ContDiffOn ℝ 1 f U) (hU : Convex ℝ U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hdim : Module.finrank ℝ E < n) :
    IsClosed (f '' K) ∧ volume (f '' K) = 0 := by
  have hc : IsCompact (f '' K) := hK.image_of_continuousOn (hf.continuousOn.mono hKU)
  refine ⟨hc.isClosed, ?_⟩
  have hd : dimH (f '' K) < (n : ℝ≥0∞) := calc
    dimH (f '' K) ≤ dimH K := hf.dimH_image_le hU hKU
    _ ≤ dimH (univ : Set E) := dimH_mono (subset_univ K)
    _ = (Module.finrank ℝ E : ℝ≥0∞) := Real.dimH_univ_eq_finrank E
    _ < n := by exact_mod_cast hdim
  have hz := hausdorffMeasure_of_dimH_lt (d := (n : ℝ≥0)) hd
  simp only [NNReal.coe_natCast] at hz
  have he := hausdorffMeasure_pi_real (ι := Fin n)
  simp only [Fintype.card_fin] at he
  rw [he] at hz
  exact hz

/-- The closure of a nonclosed parameter piece stays in the compact
null image. This conclusion does not follow from nullity alone. -/
theorem closure_smooth_image_null_of_compact_container
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {f : E → Base n} {U K S : Set E}
    (hf : ContDiffOn ℝ 1 f U) (hU : Convex ℝ U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hSK : S ⊆ K)
    (hdim : Module.finrank ℝ E < n) : volume (closure (f '' S)) = 0 := by
  obtain ⟨hc, hz⟩ := compact_smooth_image_closed_null hf hU hK hKU hdim
  exact measure_mono_null (hc.closure_subset_iff.mpr (image_mono hSK)) hz

/-- In the planar centre space, compactified zero- and one-dimensional
smooth charts supply actual closed null exceptional sets. -/
theorem compact_center_chart_closed_null {k : ℕ} (hk : k < 2)
    {c : Base k → Base 2} {U K : Set (Base k)}
    (hc : ContDiffOn ℝ 1 c U) (hU : Convex ℝ U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IsClosed (c '' K) ∧ volume (c '' K) = 0 := by
  apply compact_smooth_image_closed_null hc hU hK hKU
  simpa only [Base, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hk

theorem finite_compact_center_charts_closed_null {J : Type*} [Finite J]
    {k : J → ℕ} (hk : ∀ j, k j < 2)
    {c : (j : J) → Base (k j) → Base 2}
    {U K : (j : J) → Set (Base (k j))}
    (hc : ∀ j, ContDiffOn ℝ 1 (c j) (U j)) (hU : ∀ j, Convex ℝ (U j))
    (hK : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U j) :
    IsClosed (⋃ j, c j '' K j) ∧ volume (⋃ j, c j '' K j) = 0 := by
  have h (j : J) := compact_center_chart_closed_null (hk j) (hc j) (hU j) (hK j) (hKU j)
  exact ⟨isClosed_iUnion_of_finite (fun j => (h j).1),
    measure_iUnion_null (fun j => (h j).2)⟩

/-- An analytic arc of full parameters, including arbitrarily many
auxiliary coordinates, has a closed null centre image when its parameter
interval is compact. -/
theorem analytic_parameter_arc_center_closed_null {d : ℕ}
    (I : Interval) (c : ℝ → Parameters 2 d)
    (hc : AnalyticOnNhd ℝ c I.carrier) :
    IsClosed (Prod.fst '' (c '' I.carrier)) ∧
      volume (Prod.fst '' (c '' I.carrier)) = 0 := by
  have hcent : AnalyticOnNhd ℝ (fun t => (c t).1) I.carrier := by
    intro t ht
    exact ((ContinuousLinearMap.fst ℝ (Base 2) (Aux d)).analyticAt (c t)).comp
      (f := c) (hc t ht)
  have h := compact_smooth_image_closed_null hcent.contDiffOn_of_completeSpace
    (convex_Icc I.left I.right) isCompact_Icc Subset.rfl
    (by simp only [Module.finrank_self]; omega)
  simpa only [image_image, Function.comp_def, Interval.carrier] using h

theorem analytic_parameter_arc_center_closure_null {d : ℕ}
    (I : Interval) (c : ℝ → Parameters 2 d)
    (hc : AnalyticOnNhd ℝ c I.carrier) {S : Set ℝ} (hS : S ⊆ I.carrier) :
    volume (closure (Prod.fst '' (c '' S))) = 0 := by
  obtain ⟨hclosed, hnull⟩ := analytic_parameter_arc_center_closed_null I c hc
  exact measure_mono_null
    (hclosed.closure_subset_iff.mpr (image_mono (image_mono hS))) hnull

end PlanarNikodym
