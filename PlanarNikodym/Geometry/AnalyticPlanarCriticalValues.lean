import PlanarNikodym.Geometry.AnalyticCriticalValues
import PlanarNikodym.Geometry.PlanarCriticalLinearAlgebra
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-! Analytic Sard for planar targets, using actual analytic regular-level
charts and scalar critical-value countability. Compact images provide the
measurability needed by Fubini. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym

private theorem analytic_coordinate_fderiv {n : ℕ}
    (f : Aux n → Base 2) {x : Aux n} (hf : AnalyticAt ℝ f x) (i : Fin 2) :
    fderiv ℝ (fun y => f y i) x =
      (ContinuousLinearMap.proj i : Base 2 →L[ℝ] ℝ).comp (fderiv ℝ f x) := by
  exact ((ContinuousLinearMap.proj i : Base 2 →L[ℝ] ℝ).hasFDerivAt.comp x
    hf.differentiableAt.hasFDerivAt).fderiv

theorem analytic_planar_regular_level_critical_values_countable {n : ℕ}
    (f : Aux n → Base 2) {U : Set (Aux n)} (ho : IsOpen U)
    (ha : AnalyticOnNhd ℝ f U) (a : ℝ) :
    ((fun x => f x 1) '' {x | x ∈ U ∧ f x 0 = a ∧
      fderiv ℝ (fun y => f y 0) x ≠ 0 ∧
      ¬ Function.Surjective (fderiv ℝ f x)}).Countable := by
  classical
  cases n with
  | zero => exact (Set.to_countable _).image _
  | succ n =>
    let g (x : Aux (n + 1)) := f x 0 - a
    have ha0 : AnalyticOnNhd ℝ (fun x => f x 0) U := fun x hx =>
      ((ContinuousLinearMap.proj 0 : Base 2 →L[ℝ] ℝ).analyticAt _).comp (ha x hx)
    have ha1 : AnalyticOnNhd ℝ (fun x => f x 1) U := fun x hx =>
      ((ContinuousLinearMap.proj 1 : Base 2 →L[ℝ] ℝ).analyticAt _).comp (ha x hx)
    have hg : AnalyticOnNhd ℝ g U := fun x hx => (ha0 x hx).sub analyticAt_const
    have hex (j : Fin (n + 1)) :=
      exists_countable_regular_analytic_zero_charts g ho hg j
    choose C hC hprop hcover using hex
    have hcrit (j : Fin (n + 1)) (Q : AnalyticDimensionDropChart (n + 1) U) (hQ : Q ∈ C j) :
        ((fun v => f (Q.map v) 1) '' {v | v ∈ Q.source ∧
          fderiv ℝ (fun w => f (Q.map w) 1) v = 0}).Countable :=
      analytic_critical_values_countable Q.dim _ Q.open_source
        (fun v hv => (ha1 (Q.map v) (Q.maps_to hv)).comp (Q.analytic_map v hv))
    have hcnt := Set.countable_iUnion fun j =>
      (hC j).biUnion fun Q hQ => hcrit j Q hQ
    apply hcnt.mono
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := exists_coordinate_derivative_ne_zero
      (fderiv ℝ (fun y => f y 0) x) hx.2.2.1
    have hgj : fderiv ℝ g x (Pi.single j 1) ≠ 0 := by
      simpa only [g, fderiv_fun_sub (ha0 x hx.1).differentiableAt
        (differentiableAt_const a), fderiv_const_apply, sub_zero] using hj
    obtain ⟨Q, hQ, v, hv, hev⟩ :=
      hcover j x hx.1 (sub_eq_zero.mpr hx.2.1) hgj
    refine mem_iUnion.mpr ⟨j, mem_iUnion₂.mpr ⟨Q, hQ, v, ⟨hv, ?_⟩,
      congrArg (fun y => f y 1) hev⟩⟩
    have hmap := Q.analytic_map v hv
    have hfx := ha (Q.map v) (Q.maps_to hv)
    have hflat : (fun w => f (Q.map w) 0) =ᶠ[𝓝 v] fun _ => a := by
      filter_upwards [Q.open_source.mem_nhds hv] with w hw
      exact sub_eq_zero.mp ((hprop j Q hQ).2 w hw)
    have hzero : fderiv ℝ (fun w => f (Q.map w) 0) v = 0 := by
      rw [hflat.fderiv_eq, fderiv_const_apply]
    have hder0 := ((ContinuousLinearMap.proj 0 : Base 2 →L[ℝ] ℝ).hasFDerivAt.comp v
      (hfx.differentiableAt.hasFDerivAt.comp v hmap.differentiableAt.hasFDerivAt)).fderiv
    have hder1 := ((ContinuousLinearMap.proj 1 : Base 2 →L[ℝ] ℝ).hasFDerivAt.comp v
      (hfx.differentiableAt.hasFDerivAt.comp v hmap.differentiableAt.hasFDerivAt)).fderiv
    simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at hder0 hder1
    rw [hder1]
    ext w
    apply planar_nonsurjective_kernel_inclusion (fderiv ℝ f (Q.map v))
      (hev ▸ hx.2.2.2)
    · refine ⟨Pi.single j 1, ?_⟩
      rw [← hev, analytic_coordinate_fderiv f hfx 0] at hj
      exact hj
    · have hz := congrArg (fun L : Aux Q.dim →L[ℝ] ℝ => L w) (hder0.symm.trans hzero)
      exact hz

/-- The actual image of a compact set on which an analytic map to the plane
is everywhere critical is closed and Lebesgue-null, in arbitrary source dimension. -/
theorem compact_analytic_planar_critical_image_closed_null {n : ℕ}
    (f : Aux n → Base 2) {U K : Set (Aux n)} (ho : IsOpen U)
    (ha : AnalyticOnNhd ℝ f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hcrit : ∀ x ∈ K, ¬ Function.Surjective (fderiv ℝ f x)) :
    IsClosed (f '' K) ∧ volume (f '' K) = 0 := by
  have hfc : ContinuousOn f K :=
    fun x hx => (ha x (hKU hx)).continuousAt.continuousWithinAt
  have hcompact := hK.image_of_continuousOn hfc
  refine ⟨hcompact.isClosed, ?_⟩
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  let A : Set (ℝ × ℝ) := (fun x => (f x 0, f x 1)) '' K
  have hAc : IsCompact A :=
    hK.image_of_continuousOn (((continuous_apply 0).comp_continuousOn hfc).prodMk
      ((continuous_apply 1).comp_continuousOn hfc))
  have ha0 : AnalyticOnNhd ℝ (fun x => f x 0) U := fun x hx =>
    ((ContinuousLinearMap.proj 0 : Base 2 →L[ℝ] ℝ).analyticAt _).comp (ha x hx)
  let C := (fun x => f x 0) '' {x | x ∈ U ∧ fderiv ℝ (fun y => f y 0) x = 0}
  have hC : C.Countable := analytic_critical_values_countable n _ ho ha0
  have hAnull : volume A = 0 := by
    apply Measure.measure_prod_null_of_ae_null hAc.measurableSet
    filter_upwards [hC.ae_notMem volume] with a haC
    apply Set.Countable.measure_zero
    apply (analytic_planar_regular_level_critical_values_countable f ho ha a).mono
    rintro b ⟨x, hx, he⟩
    have he0 : f x 0 = a := congrArg Prod.fst he
    have he1 : f x 1 = b := congrArg Prod.snd he
    refine ⟨x, ⟨hKU hx, he0, ?_, hcrit x hx⟩, he1⟩
    intro hz
    exact haC ⟨x, ⟨hKU hx, hz⟩, he0⟩
  have hpre : volume (e ⁻¹' A) = 0 :=
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).preimage_null hAnull
  apply measure_mono_null (t := e ⁻¹' A) ?_ hpre
  rintro _ ⟨x, hx, rfl⟩
  exact mem_image_of_mem _ hx

theorem closure_analytic_planar_critical_image_null {n : ℕ}
    (f : Aux n → Base 2) {U K S : Set (Aux n)} (ho : IsOpen U)
    (ha : AnalyticOnNhd ℝ f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hcrit : ∀ x ∈ K, ¬ Function.Surjective (fderiv ℝ f x)) (hSK : S ⊆ K) :
    volume (closure (f '' S)) = 0 := by
  obtain ⟨hc, hn⟩ :=
    compact_analytic_planar_critical_image_closed_null f ho ha hK hKU hcrit
  exact measure_mono_null (hc.closure_subset_iff.mpr (image_mono hSK)) hn

end PlanarNikodym
