import PlanarNikodym.Projection.UniformTransverseCone
import PlanarNikodym.Projection.ProjectionBranchReduction

/-! Actual local window data for the transverse projection construction.

The data in this file is constructed from two regular points with distinct
projective slopes. It records analytic boxes and quantitative derivative bounds,
and contains no projection selection or fan construction hypothesis.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology

namespace PlanarNikodym

/-- Uniform local data extracted from two regular transverse scalar families.
The closed time window, open centre window, and spatial buffer use one radius. -/
structure LocalTransverseProjectionData
    (φ ψ : ℝ × Plane → ℝ) (U V : Set (ℝ × Plane))
    (t x : ℝ) (q : Plane) where
  radius : ℝ
  radius_pos : 0 < radius
  slopeMin : ℝ
  slopeMax : ℝ
  slope_lt : slopeMin < slopeMax
  headBound : ℝ
  headBound_pos : 0 < headBound
  derivativeLower : ℝ
  derivativeLower_pos : 0 < derivativeLower
  derivativeUpper : ℝ
  derivativeUpper_pos : 0 < derivativeUpper
  sign : ℝ
  sign_eq : sign = 1 ∨ sign = -1
  curve_domain : closedBall t radius ×ˢ closedBall q radius ⊆ U
  center_domain : closedBall x radius ×ˢ closedBall q radius ⊆ V
  curve_analytic : AnalyticOnNhd ℝ φ (closedBall t radius ×ˢ closedBall q radius)
  curve_head : ∀ p ∈ closedBall t radius ×ˢ closedBall q radius,
    scalarHeadDerivative φ p ≠ 0
  curve_head_bound : ∀ p ∈ closedBall t radius ×ˢ closedBall q radius,
    |scalarHeadDerivative φ p| ≤ headBound
  curve_slope : ∀ p ∈ closedBall t radius ×ˢ closedBall q radius,
    scalarGradientSlope φ p ∈ Icc slopeMin slopeMax
  center_analytic : AnalyticOnNhd ℝ ψ (closedBall x radius ×ˢ closedBall q radius)
  center_head : ∀ p ∈ closedBall x radius ×ˢ closedBall q radius,
    scalarHeadDerivative ψ p ≠ 0
  center_signed_norm : ∀ p ∈ closedBall x radius ×ˢ closedBall q radius,
    ‖fderiv ℝ (fun z : Plane => sign * ψ (p.1, z)) p.2‖ ≤ derivativeUpper
  center_signed_direction : ∀ p ∈ closedBall x radius ×ˢ closedBall q radius,
    ∀ s ∈ Icc slopeMin slopeMax,
      derivativeLower ≤ fderiv ℝ (fun z : Plane => sign * ψ (p.1, z)) p.2 (-s, 1)

namespace LocalTransverseProjectionData

variable {φ ψ : ℝ × Plane → ℝ} {U V : Set (ℝ × Plane)}
  {t x : ℝ} {q : Plane}
  (B : LocalTransverseProjectionData φ ψ U V t x q)

def curveTimes : Set ℝ := closedBall t B.radius
def centerTimes : Set ℝ := ball x B.radius
def parameterBuffer : Set Plane := closedBall q B.radius
def parameterDomain : Set Plane := ball q (B.radius / 2)

theorem curveTimes_compact : IsCompact B.curveTimes :=
  isCompact_closedBall _ _

theorem curveTimes_measurable : MeasurableSet B.curveTimes :=
  measurableSet_closedBall

theorem curveTimes_volume_pos : 0 < volume B.curveTimes :=
  Metric.measure_closedBall_pos volume t B.radius_pos

theorem curveTimes_volume_lt_top : volume B.curveTimes < ⊤ :=
  measure_closedBall_lt_top

theorem centerTimes_open : IsOpen B.centerTimes := isOpen_ball

theorem centerTimes_nonempty : B.centerTimes.Nonempty :=
  ⟨x, mem_ball_self B.radius_pos⟩

theorem parameterBuffer_compact : IsCompact B.parameterBuffer :=
  isCompact_closedBall _ _

theorem parameterBuffer_convex : Convex ℝ B.parameterBuffer :=
  convex_closedBall _ _

theorem parameterDomain_open : IsOpen B.parameterDomain := isOpen_ball

theorem parameterDomain_nonempty : B.parameterDomain.Nonempty :=
  ⟨q, mem_ball_self (half_pos B.radius_pos)⟩

theorem parameterDomain_convex : Convex ℝ B.parameterDomain :=
  convex_ball _ _

theorem parameterDomain_subset_buffer : B.parameterDomain ⊆ B.parameterBuffer :=
  (ball_subset_closedBall).trans
    (closedBall_subset_closedBall (half_le_self B.radius_pos.le))

theorem curveTimes_parameterDomain_subset :
    B.curveTimes ×ˢ B.parameterDomain ⊆ closedBall t B.radius ×ˢ closedBall q B.radius :=
  fun _ hp => ⟨hp.1, B.parameterDomain_subset_buffer hp.2⟩

theorem centerTimes_parameterDomain_subset :
    B.centerTimes ×ˢ B.parameterDomain ⊆ closedBall x B.radius ×ˢ closedBall q B.radius :=
  fun _ hp => ⟨ball_subset_closedBall hp.1, B.parameterDomain_subset_buffer hp.2⟩

theorem curve_continuousOn :
    ContinuousOn φ (B.curveTimes ×ˢ B.parameterDomain) :=
  B.curve_analytic.continuousOn.mono B.curveTimes_parameterDomain_subset

theorem signedCenter_continuousOn :
    ContinuousOn (fun p : ℝ × Plane => B.sign * ψ p)
      (B.centerTimes ×ˢ B.parameterDomain) :=
  continuousOn_const.mul
    (B.center_analytic.continuousOn.mono B.centerTimes_parameterDomain_subset)

theorem signedCenter_differentiableAt (a : ℝ) (ha : a ∈ B.centerTimes)
    (z : Plane) (hz : z ∈ B.parameterDomain) :
    DifferentiableAt ℝ (fun w : Plane => B.sign * ψ (a, w)) z := by
  have h := (B.center_analytic (a, z)
    (B.centerTimes_parameterDomain_subset ⟨ha, hz⟩)).differentiableAt
  exact (h.comp z (by fun_prop)).const_mul B.sign

theorem signedCenter_norm_le (a : ℝ) (ha : a ∈ B.centerTimes)
    (z : Plane) (hz : z ∈ B.parameterDomain) :
    ‖fderiv ℝ (fun w : Plane => B.sign * ψ (a, w)) z‖ ≤ B.derivativeUpper :=
  B.center_signed_norm (a, z) (B.centerTimes_parameterDomain_subset ⟨ha, hz⟩)

theorem signedCenter_direction_le (a : ℝ) (ha : a ∈ B.centerTimes)
    (z : Plane) (hz : z ∈ B.parameterDomain)
    (s : ℝ) (hs : s ∈ Icc B.slopeMin B.slopeMax) :
    B.derivativeLower ≤ fderiv ℝ (fun w : Plane => B.sign * ψ (a, w)) z (-s, 1) :=
  B.center_signed_direction (a, z)
    (B.centerTimes_parameterDomain_subset ⟨ha, hz⟩) s hs

theorem signedCenter_fixed_direction_pos (a : ℝ) (ha : a ∈ B.centerTimes)
    (z : Plane) (hz : z ∈ B.parameterDomain) :
    0 < fderiv ℝ (fun w : Plane => B.sign * ψ (a, w)) z (-B.slopeMin, 1) :=
  B.derivativeLower_pos.trans_le
    (B.signedCenter_direction_le a ha z hz B.slopeMin ⟨le_rfl, B.slope_lt.le⟩)

end LocalTransverseProjectionData

/-- Continuity and compactness construct every local bound from the two
transverse regular points, including the actual signed spatial derivatives. -/
theorem exists_localTransverseProjectionData
    {φ ψ : ℝ × Plane → ℝ} {U V : Set (ℝ × Plane)}
    (hU : IsOpen U) (hV : IsOpen V) (t x : ℝ) (q : Plane)
    (htq : (t, q) ∈ U) (hxq : (x, q) ∈ V)
    (hφ : AnalyticAt ℝ φ (t, q)) (hψ : AnalyticAt ℝ ψ (x, q))
    (hhφ : scalarHeadDerivative φ (t, q) ≠ 0)
    (hhψ : scalarHeadDerivative ψ (x, q) ≠ 0)
    (hne : scalarGradientSlope φ (t, q) ≠ scalarGradientSlope ψ (x, q)) :
    Nonempty (LocalTransverseProjectionData φ ψ U V t x q) := by
  obtain ⟨r, hr, ρ, hρ, m, hm, M, hM, σ, hσ, hrU, hrV, hφr, hψr, hcone⟩ :=
    exists_separated_scalar_uniform_transverse_cone hU hV t x q htq hxq
      hφ hψ hhφ hhψ hne
  have hhead : ContinuousOn (scalarHeadDerivative φ) (closedBall (t, q) r) :=
    fun z hz => (scalarHeadDerivative_analyticAt (hφr z hz).1).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (t, q) r).exists_bound_of_continuousOn hhead
  have hpair {a : ℝ} {p : ℝ × Plane}
      (hp : p ∈ closedBall a r ×ˢ closedBall q r) : p ∈ closedBall (a, q) r := by
    rwa [← closedBall_prod_same]
  refine ⟨{
    radius := r
    radius_pos := hr
    slopeMin := scalarGradientSlope φ (t, q) - ρ
    slopeMax := scalarGradientSlope φ (t, q) + ρ
    slope_lt := by linarith
    headBound := max C 1
    headBound_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    derivativeLower := m
    derivativeLower_pos := hm
    derivativeUpper := M
    derivativeUpper_pos := hM
    sign := σ
    sign_eq := hσ
    curve_domain := fun _ hp => hrU (hpair hp)
    center_domain := fun _ hp => hrV (hpair hp)
    curve_analytic := fun z hz => (hφr z (hpair hz)).1
    curve_head := fun z hz => (hφr z (hpair hz)).2.1
    curve_head_bound := ?_
    curve_slope := ?_
    center_analytic := fun z hz => (hψr z (hpair hz)).1
    center_head := fun z hz => (hψr z (hpair hz)).2.1
    center_signed_norm := ?_
    center_signed_direction := ?_
  }⟩
  · intro z hz
    have hb : |scalarHeadDerivative φ z| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC z (hpair hz)
    exact hb.trans (le_max_left C 1)
  · intro z hz
    simpa only [Real.closedBall_eq_Icc] using (hφr z (hpair hz)).2.2
  · intro z hz
    exact (norm_signed_scalarSlice_fderiv_le
      (hψr z (hpair hz)).1.differentiableAt hσ).trans (hψr z (hpair hz)).2.2
  · intro z hz s hs
    rw [signed_scalarSlice_fderiv_apply (hψr z (hpair hz)).1.differentiableAt]
    exact hcone z (hpair hz) s (by simpa only [Real.closedBall_eq_Icc] using hs)

namespace ProjectionModel

variable {d : ℕ} (D : ProjectionModel d)

/-- The actual parameter domain on which the two-slice remains inside the model. -/
def twoSliceParameterDomain (j : Fin (d + 1)) : Set Plane :=
  twoParameterInsert D.base.2 j ⁻¹' ball D.base.2 D.radius

def twoSliceCurveDomain (j : Fin (d + 1)) : Set (ℝ × Plane) :=
  Ioo D.I.left D.I.right ×ˢ D.twoSliceParameterDomain j

def twoSliceCenterDomain (j : Fin (d + 1)) : Set (ℝ × Plane) :=
  ball D.base.1 D.radius ×ˢ D.twoSliceParameterDomain j

theorem twoSliceParameterDomain_open (j : Fin (d + 1)) :
    IsOpen (D.twoSliceParameterDomain j) :=
  isOpen_ball.preimage
    (continuousOn_univ.mp (twoParameterInsert_analytic D.base.2 j).continuousOn)

theorem twoSliceCurveDomain_open (j : Fin (d + 1)) :
    IsOpen (D.twoSliceCurveDomain j) :=
  isOpen_Ioo.prod (D.twoSliceParameterDomain_open j)

theorem twoSliceCenterDomain_open (j : Fin (d + 1)) :
    IsOpen (D.twoSliceCenterDomain j) :=
  isOpen_ball.prod (D.twoSliceParameterDomain_open j)

/-- A separated regular pair of actual two-slices produces the uniform windows
needed by the nonlinear fan and compact refinement construction. -/
theorem exists_twoSlice_localTransverseProjectionData
    (j : Fin (d + 1)) (t x : ℝ) (q : Plane)
    (ht : t ∈ Ioo D.I.left D.I.right) (hx : x ∈ ball D.base.1 D.radius)
    (hq : twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius)
    (hhφ : scalarHeadDerivative (D.twoSliceCurves j) (t, q) ≠ 0)
    (hhψ : scalarHeadDerivative (D.twoSliceCenters j) (x, q) ≠ 0)
    (hne : scalarGradientSlope (D.twoSliceCurves j) (t, q) ≠
      scalarGradientSlope (D.twoSliceCenters j) (x, q)) :
    Nonempty (LocalTransverseProjectionData (D.twoSliceCurves j) (D.twoSliceCenters j)
      (D.twoSliceCurveDomain j) (D.twoSliceCenterDomain j) t x q) := by
  exact exists_localTransverseProjectionData
    (D.twoSliceCurveDomain_open j) (D.twoSliceCenterDomain_open j) t x q
    ⟨ht, hq⟩ ⟨hx, hq⟩
    (D.twoSliceCurves_analyticAt j (t, q) ⟨ht.1.le, ht.2.le⟩ hq)
    (D.twoSliceCenters_analyticAt j (x, q) hx hq) hhφ hhψ hne

/-- The stationary branch is already a null-set construction. The other branch
now returns fully constructed quantitative local data, with no residual
nonstationarity assumptions and no assumed projection selection. -/
theorem exists_null_set_or_twoSlice_localTransverseProjectionData (hd : 0 < d) :
    (∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E)) ∨
    ∃ j : Fin (d + 1), ∃ t x : ℝ, ∃ q : Plane, j ≠ 0 ∧
      Nonempty (LocalTransverseProjectionData (D.twoSliceCurves j) (D.twoSliceCenters j)
        (D.twoSliceCurveDomain j) (D.twoSliceCenterDomain j) t x q) := by
  rcases D.exists_null_set_or_separated_twoSlice_points hd with hE |
    ⟨j, t, x, q, hj, ht, hx, hq, hhφ, hhψ, _, _, hne⟩
  · exact Or.inl hE
  · exact Or.inr ⟨j, t, x, q, hj,
      D.exists_twoSlice_localTransverseProjectionData j t x q ht hx hq hhφ hhψ hne⟩

end ProjectionModel

namespace LocalTransverseProjectionData

variable {d : ℕ} {D : ProjectionModel d} {j : Fin (d + 1)}
  {t x : ℝ} {q : Plane}
  (B : LocalTransverseProjectionData (D.twoSliceCurves j) (D.twoSliceCenters j)
    (D.twoSliceCurveDomain j) (D.twoSliceCenterDomain j) t x q)

theorem twoSlice_curveTimes_subset : B.curveTimes ⊆ Ioo D.I.left D.I.right := by
  intro a ha
  have hp : (a, q) ∈ closedBall t B.radius ×ˢ closedBall q B.radius :=
    ⟨ha, mem_closedBall_self B.radius_pos.le⟩
  exact (B.curve_domain hp).1

theorem twoSlice_centerTimes_subset : B.centerTimes ⊆ ball D.base.1 D.radius := by
  intro a ha
  have hp : (a, q) ∈ closedBall x B.radius ×ˢ closedBall q B.radius :=
    ⟨ball_subset_closedBall ha, mem_closedBall_self B.radius_pos.le⟩
  exact (B.center_domain hp).1

theorem twoSlice_parameterBuffer_subset :
    B.parameterBuffer ⊆ D.twoSliceParameterDomain j := by
  intro z hz
  have hp : (t, z) ∈ closedBall t B.radius ×ˢ closedBall q B.radius :=
    ⟨mem_closedBall_self B.radius_pos.le, hz⟩
  exact (B.curve_domain hp).2

theorem twoSlice_parameterDomain_subset :
    B.parameterDomain ⊆ D.twoSliceParameterDomain j :=
  B.parameterDomain_subset_buffer.trans B.twoSlice_parameterBuffer_subset

end LocalTransverseProjectionData

end PlanarNikodym
