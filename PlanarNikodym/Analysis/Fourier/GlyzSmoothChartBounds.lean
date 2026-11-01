import PlanarNikodym.Analysis.Fourier.GlyzSmoothJetCoordinates
import PlanarNikodym.Analysis.Fourier.ParametricChartBounds

/-! Uniform actual Jacobians and change of variables for the C∞
retained time-jet charts, including anisotropic parabolic dilation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PlanarNikodym

theorem glyz_smooth_chartJacobian_ne_zero {m : ℕ}
    (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x)
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x)
    {x : Aux m} (hx : x ∈ e.source) :
    LinearMap.det (fderiv ℝ e x).toLinearMap ≠ 0 := by
  have hcomp := (((hi (e x) (e.map_source hx)).differentiableAt (by simp)).hasFDerivAt.comp x
    ((he x hx).differentiableAt (by simp)).hasFDerivAt)
  have hevent : (fun z => e.symm (e z)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    exact e.left_inv hz
  have hid : HasFDerivAt id ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) x :=
    hcomp.congr_of_eventuallyEq hevent.symm
  have hdet := congrArg (fun L : Aux m →L[ℝ] Aux m => LinearMap.det L.toLinearMap)
    (hid.unique (hasFDerivAt_id x))
  change LinearMap.det ((fderiv ℝ e.symm (e x)).toLinearMap.comp
    (fderiv ℝ e x).toLinearMap) = LinearMap.det (LinearMap.id) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  exact right_ne_zero_of_mul_eq_one hdet

theorem glyz_retainedParameterFiber_smooth
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph (P × E) (P × E)) (he : ∀ x, (e x).1 = x.1)
    (ha : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x)
    (hb : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) (p : P) :
    (∀ z ∈ (retainedParameterFiber e he p).source,
      ContDiffAt ℝ ∞ (retainedParameterFiber e he p) z) ∧
    ∀ y ∈ (retainedParameterFiber e he p).target,
      ContDiffAt ℝ ∞ (retainedParameterFiber e he p).symm y := by
  constructor
  · intro z hz
    exact ((ha (p, z) hz).comp z (contDiffAt_const.prodMk contDiffAt_id)).snd
  · intro y hy
    exact ((hb (p, y) hy).comp y (contDiffAt_const.prodMk contDiffAt_id)).snd

theorem glyz_continuousOn_fiberChartJacobian
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] {m : ℕ}
    (e : OpenPartialHomeomorph (P × Aux m) (P × Aux m))
    (ha : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) :
    ContinuousOn (fiberChartJacobian e) e.source := by
  intro x hx
  have hswap : ContDiffAt ℝ ∞ (fun y : Aux m × P => (e (y.2, y.1)).2) (x.2, x.1) :=
    ((ha x hx).comp (x.2, x.1) (contDiffAt_snd.prodMk contDiffAt_fst)).snd
  have hD : ContinuousAt (fun y : P × Aux m =>
      fderiv ℝ (fun z => (e (y.1, z)).2) y.2) x :=
    (contDiffAt_fiber_fderiv hswap).continuousAt.comp
      (f := fun y : P × Aux m => (y.2, y.1))
      (continuous_snd.prodMk continuous_fst).continuousAt
  exact (ContinuousLinearMap.continuous_det.continuousAt.comp hD).continuousWithinAt

theorem exists_glyz_uniform_fiberChartJacobian_bounds
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] {m : ℕ}
    (e : OpenPartialHomeomorph (P × Aux m) (P × Aux m))
    (he : ∀ x, (e x).1 = x.1)
    (ha : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x)
    (hb : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x)
    {K : Set (P × Aux m)} (hK : IsCompact K) (hKS : K ⊆ e.source) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ x ∈ K,
      b ≤ |fiberChartJacobian e x| ∧ |fiberChartJacobian e x| ≤ C := by
  have hc : ContinuousOn (fun x => |fiberChartJacobian e x|) K :=
    (glyz_continuousOn_fiberChartJacobian e ha).abs.mono hKS
  have hn (x : P × Aux m) (hx : x ∈ K) : 0 < |fiberChartJacobian e x| := by
    obtain ⟨ha', hb'⟩ := glyz_retainedParameterFiber_smooth e he ha hb x.1
    exact abs_pos.mpr (glyz_smooth_chartJacobian_ne_zero (retainedParameterFiber e he x.1)
      ha' hb' (hKS hx))
  obtain ⟨b, hb0, hlow⟩ := hK.exists_forall_le' hc hn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨b, |C| + 1, hb0, by positivity, ?_⟩
  intro x hx
  refine ⟨hlow x hx, ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs, abs_abs] at h
  linarith [le_abs_self C]

theorem exists_glyz_uniform_smooth_jet_bound
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S K : Set E} (ha : ∀ x ∈ S, ContDiffAt ℝ ∞ f x)
    (hK : IsCompact K) (hKS : K ⊆ S) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ j f) K := by
    intro x hx
    exact ((ha x (hKS hx)).continuousAt_iteratedFDeriv (k := j)
      (WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top))).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨|C|, abs_nonneg _, fun x hx => (hC x hx).trans (le_abs_self C)⟩

theorem glyz_integral_smooth_chart_target {m : ℕ}
    (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) (F : Aux m → ℂ) :
    (∫ y in e.target, F y) = ∫ z in e.source,
      |LinearMap.det (fderiv ℝ e z).toLinearMap| • F (e z) := by
  have himage : e '' e.source = e.target := PartialEquiv.image_source_eq_target e.toPartialEquiv
  rw [← himage]
  exact integral_image_eq_integral_abs_det_fderiv_smul volume e.open_source.measurableSet
    (fun z hz => ((he z hz).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt) e.injOn F

theorem glyz_lintegral_smooth_chart_target {m : ℕ}
    (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) (F : Aux m → ℝ≥0∞) :
    (∫⁻ y in e.target, F y) = ∫⁻ z in e.source,
      ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| * F (e z) := by
  have himage : e '' e.source = e.target := PartialEquiv.image_source_eq_target e.toPartialEquiv
  rw [← himage]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume e.open_source.measurableSet
    (fun z hz => ((he z hz).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt) e.injOn F

theorem glyz_integral_scaled_smooth_chart_target {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) (δ : ℝ) (hδ : δ ≠ 0)
    (F : Aux (n + 1) → ℂ) :
    (∫ w in lowerDegreeDilation n δ hδ '' e.target, F w) =
      |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| •
        ∫ z in e.source, |LinearMap.det (fderiv ℝ e z).toLinearMap| •
          F (lowerDegreeDilation n δ hδ (e z)) := by
  let D := lowerDegreeDilation n δ hδ
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume e.open_target.measurableSet
    (f' := fun _ => D.toContinuousLinearMap)
    (fun _ _ => D.hasFDerivAt.hasFDerivWithinAt) D.injective.injOn F]
  change (∫ x in e.target, |LinearMap.det D.toLinearMap| • F (D x)) = _
  rw [show LinearMap.det D.toLinearMap = ∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n
    from det_lowerDegreeDilation n δ hδ, integral_smul, glyz_integral_smooth_chart_target e he]

theorem glyz_lintegral_scaled_smooth_chart_target {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) (δ : ℝ) (hδ : δ ≠ 0)
    (F : Aux (n + 1) → ℝ≥0∞) :
    (∫⁻ w in lowerDegreeDilation n δ hδ '' e.target, F w) =
      ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| *
        ∫⁻ z in e.source, ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| *
          F (lowerDegreeDilation n δ hδ (e z)) := by
  let D := lowerDegreeDilation n δ hδ
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume e.open_target.measurableSet
    (f' := fun _ => D.toContinuousLinearMap)
    (fun _ _ => D.hasFDerivAt.hasFDerivWithinAt) D.injective.injOn F]
  change (∫⁻ x in e.target, ENNReal.ofReal |LinearMap.det D.toLinearMap| * F (D x)) = _
  rw [show LinearMap.det D.toLinearMap = ∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n
    from det_lowerDegreeDilation n δ hδ, lintegral_const_mul', glyz_lintegral_smooth_chart_target e he]
  exact ENNReal.ofReal_ne_top

end PlanarNikodym
