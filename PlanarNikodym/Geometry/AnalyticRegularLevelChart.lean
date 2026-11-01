import PlanarNikodym.Geometry.AnalyticImplicit
import PlanarNikodym.Cells.RegularAuxiliaryCharts
import PlanarNikodym.Geometry.AnalyticStratificationChartTopology
import PlanarNikodym.Geometry.RegularStratumEquations
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! A scalar regular level chart with its actual tangent kernel. The
implicit function is built at the specified point; the source is a
connected bounded ball, and the chosen derivative stays nonzero. -/
noncomputable section
open Set Filter Metric Module
open scoped Topology
namespace PlanarNikodym

theorem exists_analytic_regular_level_chart {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) {U : Set (Fin (n + 1) → ℝ)}
    (ho : IsOpen U) (ha : AnalyticOnNhd ℝ f U)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ U)
    (j : Fin (n + 1)) (hj : fderiv ℝ f x (Pi.single j 1) ≠ 0) :
    ∃ (P : AnalyticStratificationChart (Fin (n + 1) → ℝ)) (q : Fin P.dim → ℝ),
      P.dim = n ∧ q ∈ P.source ∧ P.map q = x ∧ P.image ⊆ U ∧
      (∀ y ∈ P.image, f y = f x ∧ fderiv ℝ f y (Pi.single j 1) ≠ 0) ∧
      (fderiv ℝ P.map q).toLinearMap.range = (fderiv ℝ f x).toLinearMap.ker := by
  let E := realCoordinateSplitEquiv j
  let a := (E.symm x).1
  let b := (E.symm x).2
  let R : (Fin n → ℝ) × ℝ → ℝ := fun z => f (E z) - f x
  have he : E (a, b) = x := E.apply_symm_apply x
  have hR : AnalyticAt ℝ R (a, b) := by
    exact ((he ▸ ha x hx).comp (E.analyticAt (a, b))).sub analyticAt_const
  have hz : R (a, b) = 0 := by simp only [R, he, sub_self]
  have hv : fderiv ℝ R (a, b) (0, 1) ≠ 0 := by
    rw [fderiv_fun_sub ((he ▸ ha x hx).comp (E.analyticAt (a, b))).differentiableAt
      (differentiableAt_const _), fderiv_const_apply, sub_zero]
    change fderiv ℝ (f ∘ E) (a, b) (0, 1) ≠ 0
    rw [fderiv_comp (a, b) (he ▸ ha x hx).differentiableAt E.differentiableAt, E.fderiv]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      E, realCoordinateSplitEquiv_vertical, he] using hj
  obtain ⟨κ, hκ, hκa, hzero, _⟩ := exists_analytic_implicit R a b hR hz
    (real_clm_isInvertible_of_apply_one_ne_zero _ hv)
  let Φ : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun z => E (z, κ z)
  have hΦa : AnalyticAt ℝ Φ a := (E.analyticAt _).comp (analyticAt_id.prod hκ)
  have hΦx : Φ a = x := by simp only [Φ, hκa, he]
  have hder : ContinuousAt (fun y => fderiv ℝ f y (Pi.single j 1)) x :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)).continuous.continuousAt.comp
      (ha x hx).fderiv.continuousAt)
  have hnear : ∀ᶠ z in 𝓝 a, AnalyticAt ℝ κ z ∧ Φ z ∈ U ∧
      R (z, κ z) = 0 ∧ fderiv ℝ f (Φ z) (Pi.single j 1) ≠ 0 := by
    have hmap := hΦa.continuousAt.preimage_mem_nhds
      (by rw [hΦx]; exact ho.mem_nhds hx)
    have ht : Tendsto Φ (𝓝 a) (𝓝 x) := hΦx ▸ hΦa.continuousAt.tendsto
    have hnon := ht.eventually (hder.eventually_ne hj)
    filter_upwards [hκ.eventually_analyticAt, hmap, hzero, hnon] with z hza hzu hzz hzn
    exact ⟨hza, hzu, hzz, hzn⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let P : AnalyticStratificationChart (Fin (n + 1) → ℝ) :=
    { dim := n
      source := ball a r
      open_source := isOpen_ball
      bounded_source := isBounded_ball
      connected_source := (convex_ball a r).isConnected (nonempty_ball.mpr hr)
      map := Φ
      inverse := fun y => (E.symm y).1
      analytic_map := fun z hz => (E.analyticAt _).comp
        (analyticAt_id.prod (hball (ball_subset_closedBall hz)).1)
      continuous_inverse := (continuous_fst.comp E.symm.continuous).continuousOn
      left_inverse := by intro z _; exact congrArg Prod.fst (E.symm_apply_apply (z, κ z))
      derivative_injective := by
        intro z hz
        apply AnalyticStratificationChart.fderiv_injective_of_factor isOpen_ball hz Φ id
          (fun y => (E.symm y).1)
          ((E.analyticAt _).comp
            (analyticAt_id.prod (hball (ball_subset_closedBall hz)).1)).differentiableAt
          (analyticAt_fst.comp (E.symm.analyticAt _)).differentiableAt
          (fun w _ => congrArg Prod.fst (E.symm_apply_apply (w, κ w)))
        rw [fderiv_id]
        exact Function.injective_id }
  have hPU : P.image ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hball (ball_subset_closedBall hz)).2.1
  have hPf : ∀ y ∈ P.image, f y = f x ∧ fderiv ℝ f y (Pi.single j 1) ≠ 0 := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨sub_eq_zero.mp (hball (ball_subset_closedBall hz)).2.2.1,
      (hball (ball_subset_closedBall hz)).2.2.2⟩
  refine ⟨P, a, rfl, mem_ball_self hr, hΦx, hPU, hPf, ?_⟩
  have hle : (fderiv ℝ P.map a).toLinearMap.range ≤ (fderiv ℝ f x).toLinearMap.ker := by
    have hevent : f ∘ P.map =ᶠ[𝓝 a] fun _ => f x := by
      filter_upwards [P.open_source.mem_nhds (mem_ball_self hr)] with z hz
      exact (hPf _ (mem_image_of_mem _ hz)).1
    have hd := hevent.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp a (ha _ (hPU (mem_image_of_mem _ (mem_ball_self hr)))).differentiableAt
      (P.analytic_map a (mem_ball_self hr)).differentiableAt, fderiv_const_apply] at hd
    rintro _ ⟨v, rfl⟩
    have hv := congrArg (fun A : (Fin n → ℝ) →L[ℝ] ℝ => A v) hd
    change fderiv ℝ f x (fderiv ℝ P.map a v) = 0
    change fderiv ℝ f (P.map a) (fderiv ℝ P.map a v) = 0 at hv
    have hPa : P.map a = x := hΦx
    rwa [hPa] at hv
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hPdim := LinearMap.finrank_range_of_inj (P.derivative_injective a (mem_ball_self hr))
  have hfdim := (fderiv ℝ f x).toLinearMap.finrank_range_add_finrank_ker
  have hsurj : Function.Surjective (fderiv ℝ f x) := by
    intro t
    refine ⟨(t / fderiv ℝ f x (Pi.single j 1)) • Pi.single j 1, ?_⟩
    simp only [map_smul, smul_eq_mul, div_mul_cancel₀ _ hj]
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self,
    finrank_fin_fun] at hfdim
  simp only [P, finrank_fin_fun] at hPdim
  change finrank ℝ (fderiv ℝ P.map a).toLinearMap.range = _
  change finrank ℝ (fderiv ℝ Φ a).toLinearMap.range = _
  omega

end PlanarNikodym
