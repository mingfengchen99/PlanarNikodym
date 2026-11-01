import PlanarNikodym.Geometry.AnalyticPlanarCriticalValues
import PlanarNikodym.Cells.CompactCriticalCenters

/-! Actual closed null critical-center images, with arbitrary source dimension.
The compact critical locus is constructed from the derivative and not postulated. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem isClosed_setOf_planar_not_surjective {n : ℕ} :
    IsClosed {L : Aux n →L[ℝ] Base 2 | ¬ Function.Surjective L} := by
  have he : {L : Aux n →L[ℝ] Base 2 | ¬ Function.Surjective L} =
      ⋂ v, ⋂ w, {L | L v 0 * L w 1 - L v 1 * L w 0 = 0} := by
    ext L
    simp only [mem_setOf_eq, mem_iInter, planar_not_surjective_iff_minors_zero]
  rw [he]
  have hc (v : Aux n) (i : Fin 2) :
      Continuous (fun L : Aux n →L[ℝ] Base 2 => L v i) :=
    (continuous_apply i).comp (continuous_id.clm_apply continuous_const)
  exact isClosed_iInter fun v => isClosed_iInter fun w =>
    isClosed_eq ((hc v 0).mul (hc w 1) |>.sub ((hc v 1).mul (hc w 0))) continuous_const

/-- Analytic Sard on the whole actual critical subset of any compact container. -/
theorem compact_analytic_critical_center_image_closed_null {n : ℕ}
    (f : Aux n → Base 2) {U K : Set (Aux n)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IsClosed (f '' {x | x ∈ K ∧ ¬ Function.Surjective (fderiv ℝ f x)}) ∧
      volume (f '' {x | x ∈ K ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  have hdc : ContinuousOn (fderiv ℝ f) K := fun x hx =>
    ((ha x (hKU hx)).contDiffAt (n := 1)).continuousAt_fderiv
      (by norm_num) |>.continuousWithinAt
  have hSc : IsClosed {x | x ∈ K ∧ ¬ Function.Surjective (fderiv ℝ f x)} :=
    hdc.preimage_isClosed_of_isClosed hK.isClosed isClosed_setOf_planar_not_surjective
  have hS : IsCompact {x | x ∈ K ∧ ¬ Function.Surjective (fderiv ℝ f x)} :=
    hK.of_isClosed_subset hSc (fun _ hx => hx.1)
  exact compact_analytic_planar_critical_image_closed_null f ho ha hS
    (fun _ hx => hKU hx.1) (fun _ hx => hx.2)

/-- Any critical subset of the compact container has null image closure.
The closure lies in the actual compact critical image proved above. -/
theorem closure_analytic_critical_center_image_null {n : ℕ}
    (f : Aux n → Base 2) {U K S : Set (Aux n)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hSK : S ⊆ K)
    (hc : ∀ x ∈ S, ¬ Function.Surjective (fderiv ℝ f x)) :
    volume (closure (f '' S)) = 0 := by
  obtain ⟨hclosed, hnull⟩ :=
    compact_analytic_critical_center_image_closed_null f ho ha hK hKU
  exact measure_mono_null (hclosed.closure_subset_iff.mpr
    (image_mono (fun x hx => ⟨hSK hx, hc x hx⟩))) hnull

theorem compact_analytic_rank_lt_two_center_image_closed_null {n : ℕ}
    (f : Aux n → Base 2) {U K : Set (Aux n)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hrank : ∀ x ∈ K, Module.finrank ℝ (fderiv ℝ f x).toLinearMap.range < 2) :
    IsClosed (f '' K) ∧ volume (f '' K) = 0 := by
  apply compact_analytic_planar_critical_image_closed_null f ho ha hK hKU
  intro x hx hs
  have hr := hrank x hx
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  norm_num [Base, Module.finrank_pi] at hr

/-- Analytic Sard on an arbitrary open source domain. This conclusion asserts
nullity, not closedness; only the compact-container theorems control closures. -/
theorem analytic_planar_critical_image_null {n : ℕ}
    (f : Aux n → Base 2) {U : Set (Aux n)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  letI : LocallyCompactSpace U := ho.locallyCompactSpace
  have hsc : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hsc
  have hKU (i : ℕ) : K i ⊆ U := by
    rw [← hcover]
    exact subset_iUnion K i
  have hn (i : ℕ) := (compact_analytic_critical_center_image_closed_null
    f ho ha (hK i) (hKU i)).2
  apply measure_mono_null (t := ⋃ i, f '' {x | x ∈ K i ∧
    ¬ Function.Surjective (fderiv ℝ f x)}) ?_ (measure_iUnion_null hn)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hx.1)
  exact mem_iUnion.mpr ⟨i, mem_image_of_mem f ⟨hi, hx.2⟩⟩

/-- Application to the actual center projection of any analytic full-parameter
parametrization, before conversion to a center-preserving retained piece. -/
theorem compact_analytic_parameter_critical_centers_closed_null {n d : ℕ}
    (c : Aux n → Parameters 2 d) {U K : Set (Aux n)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ c U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    IsClosed (Prod.fst '' (c '' {x | x ∈ K ∧
      ¬ Function.Surjective (fderiv ℝ (fun y => (c y).1) x)})) ∧
      volume (Prod.fst '' (c '' {x | x ∈ K ∧
        ¬ Function.Surjective (fderiv ℝ (fun y => (c y).1) x)})) = 0 := by
  have hc : AnalyticOnNhd ℝ (fun y => (c y).1) U :=
    fun x hx => analyticAt_fst.comp (ha x hx)
  simpa only [image_image, Function.comp_def] using
    compact_analytic_critical_center_image_closed_null (fun y => (c y).1)
      ho hc hK hKU

end PlanarNikodym
