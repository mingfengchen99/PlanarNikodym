import PlanarNikodym.Geometry.CinematicLowerCoordinates
import PlanarNikodym.Analysis.Fourier.LowerDegreePhaseScaling

/-! The actual nonlinear chart and anisotropic coefficient dilation have
an exact combined Lebesgue change of variables. On a compact subset of a
fixed analytic chart, the nonlinear Jacobian has genuine two-sided bounds. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PlanarNikodym

theorem analyticAt_chartJacobian {m : ℕ} {e : OpenPartialHomeomorph (Aux m) (Aux m)}
    {x : Aux m} (he : AnalyticAt ℝ e x) :
    AnalyticAt ℝ (fun z => LinearMap.det (fderiv ℝ e z).toLinearMap) x := by
  have heq : (fun z => LinearMap.det (fderiv ℝ e z).toLinearMap) =
      fun z => Matrix.det (fun i j : Fin m => (fderiv ℝ e z) (Pi.single j 1) i) := by
    funext z
    exact (LinearMap.det_toMatrix' _).symm
  rw [heq]
  apply analyticAt_det
  intro i j
  let A : (Aux m →L[ℝ] Aux m) →L[ℝ] Aux m :=
    ContinuousLinearMap.apply ℝ (Aux m) (Pi.single j 1)
  have hv : AnalyticAt ℝ (fun z => (fderiv ℝ e z) (Pi.single j 1)) x :=
    A.analyticAt _ |>.comp (f := fderiv ℝ e) he.fderiv
  exact ((ContinuousLinearMap.proj i : Aux m →L[ℝ] ℝ).analyticAt _).comp
    (f := fun z => (fderiv ℝ e z) (Pi.single j 1)) hv

theorem analytic_chartJacobian_ne_zero {m : ℕ} (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : AnalyticOnNhd ℝ e e.source) (hi : AnalyticOnNhd ℝ e.symm e.target)
    {x : Aux m} (hx : x ∈ e.source) :
    LinearMap.det (fderiv ℝ e x).toLinearMap ≠ 0 := by
  have hcomp := ((hi (e x) (e.map_source hx)).differentiableAt.hasFDerivAt.comp x
    (he x hx).differentiableAt.hasFDerivAt)
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

theorem exists_compact_analytic_chartJacobian_bounds {m : ℕ}
    (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : AnalyticOnNhd ℝ e e.source) (hi : AnalyticOnNhd ℝ e.symm e.target)
    {K : Set (Aux m)} (hK : IsCompact K) (hKS : K ⊆ e.source) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ z ∈ K,
      b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap| ∧
        |LinearMap.det (fderiv ℝ e z).toLinearMap| ≤ C := by
  have hJ : ContinuousOn (fun z => |LinearMap.det (fderiv ℝ e z).toLinearMap|) K := by
    intro z hz
    exact (analyticAt_chartJacobian (he z (hKS hz))).continuousAt.abs.continuousWithinAt
  obtain ⟨b, hb, hlow⟩ := hK.exists_forall_le' hJ
    (fun z hz => abs_pos.mpr (analytic_chartJacobian_ne_zero e he hi (hKS hz)))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hJ
  refine ⟨b, |B| + 1, hb, by positivity, ?_⟩
  intro z hz
  refine ⟨hlow z hz, ?_⟩
  have hbound := hB z hz
  rw [Real.norm_eq_abs, abs_abs] at hbound
  linarith [le_abs_self B]

theorem integral_scaled_analytic_chart_target {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : AnalyticOnNhd ℝ e e.source) (δ : ℝ) (hδ : δ ≠ 0)
    (F : Aux (n + 1) → ℂ) :
    (∫ w in lowerDegreeDilation n δ hδ '' e.target, F w) =
      |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| •
        ∫ z in e.source, |LinearMap.det (fderiv ℝ e z).toLinearMap| •
          F (lowerDegreeDilation n δ hδ (e z)) := by
  let D := lowerDegreeDilation n δ hδ
  have hD (y : Aux (n + 1)) : HasFDerivWithinAt D D.toContinuousLinearMap e.target y :=
    D.hasFDerivAt.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume e.open_target.measurableSet
    (f' := fun _ => D.toContinuousLinearMap) (fun y _ => hD y) D.injective.injOn F]
  have hdetD : LinearMap.det D.toLinearMap = ∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n :=
    det_lowerDegreeDilation n δ hδ
  change (∫ x in e.target, |LinearMap.det D.toLinearMap| • F (D x)) = _
  rw [hdetD, integral_smul, integral_analytic_chart_target e he]

theorem lintegral_analytic_chart_target {m : ℕ} (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : AnalyticOnNhd ℝ e e.source) (F : Aux m → ℝ≥0∞) :
    (∫⁻ y in e.target, F y) = ∫⁻ z in e.source,
      ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| * F (e z) := by
  have himage : e '' e.source = e.target := PartialEquiv.image_source_eq_target e.toPartialEquiv
  rw [← himage]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume e.open_source.measurableSet
    (fun z hz => (he z hz).differentiableAt.hasFDerivAt.hasFDerivWithinAt) e.injOn F

theorem lintegral_scaled_analytic_chart_target {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : AnalyticOnNhd ℝ e e.source) (δ : ℝ) (hδ : δ ≠ 0)
    (F : Aux (n + 1) → ℝ≥0∞) :
    (∫⁻ w in lowerDegreeDilation n δ hδ '' e.target, F w) =
      ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| *
        ∫⁻ z in e.source, ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| *
          F (lowerDegreeDilation n δ hδ (e z)) := by
  let D := lowerDegreeDilation n δ hδ
  have hD (y : Aux (n + 1)) : HasFDerivWithinAt D D.toContinuousLinearMap e.target y :=
    D.hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume e.open_target.measurableSet
    (f' := fun _ => D.toContinuousLinearMap) (fun y _ => hD y) D.injective.injOn F]
  have hdetD : LinearMap.det D.toLinearMap = ∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n :=
    det_lowerDegreeDilation n δ hδ
  change (∫⁻ x in e.target, ENNReal.ofReal |LinearMap.det D.toLinearMap| * F (D x)) = _
  rw [hdetD, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_analytic_chart_target e he]

end PlanarNikodym
