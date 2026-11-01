import PlanarNikodym.Projection.NonstationaryProjectionGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Angle coordinates for the regular, nonstationary projection patches.

`Plane` carries the product norm, not the Euclidean norm. Consequently the
unit-gradient formulas below use `sqrt (head ^ 2 + tail ^ 2)` explicitly.
The principal angle describes the unoriented gradient line; a negative
head component requires adding π to recover the oriented gradient.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

/-- The principal angle of the parameter-gradient line on a nonzero-head
coordinate chart. -/
def scalarGradientAngle (ψ : ℝ × Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  Real.arctan (scalarGradientSlope ψ p)

theorem scalarGradientAngle_mem_Ioo (ψ : ℝ × Plane → ℝ) (p : ℝ × Plane) :
    scalarGradientAngle ψ p ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  Real.arctan_mem_Ioo _

theorem scalarGradientAngle_eq_iff
    (φ ψ : ℝ × Plane → ℝ) (p q : ℝ × Plane) :
    scalarGradientAngle φ p = scalarGradientAngle ψ q ↔
      scalarGradientSlope φ p = scalarGradientSlope ψ q :=
  Real.arctan_inj

theorem scalarGradientAngle_continuousAt
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : AnalyticAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0) :
    ContinuousAt (scalarGradientAngle ψ) p :=
  Real.continuous_arctan.continuousAt.comp
    (scalarGradientSlope_analyticAt hψ hh).continuousAt

/-- The angle derivative has exactly the sign of the projective slope
derivative. The denominator is strictly positive everywhere. -/
theorem scalarGradientAngle_deriv
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : AnalyticAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0) :
    deriv (fun t => scalarGradientAngle ψ (t, p.2)) p.1 =
      deriv (fun t => scalarGradientSlope ψ (t, p.2)) p.1 /
        (1 + scalarGradientSlope ψ p ^ 2) := by
  have hs : DifferentiableAt ℝ (fun t => scalarGradientSlope ψ (t, p.2)) p.1 :=
    ((scalarGradientSlope_analyticAt hψ hh).comp
      (f := fun t : ℝ => (t, p.2)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  simpa only [scalarGradientAngle, one_div, div_eq_mul_inv, mul_comm, one_mul,
    Prod.mk.eta] using
    deriv_arctan hs

theorem scalarGradientAngle_deriv_ne_zero_iff
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : AnalyticAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0) :
    deriv (fun t => scalarGradientAngle ψ (t, p.2)) p.1 ≠ 0 ↔
      deriv (fun t => scalarGradientSlope ψ (t, p.2)) p.1 ≠ 0 := by
  rw [scalarGradientAngle_deriv hψ hh]
  constructor
  · exact fun h => (div_ne_zero_iff.mp h).1
  · exact fun h => div_ne_zero h (by positivity)

theorem scalarGradientAngle_oriented_deriv_pos
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane} (σ : ℝ)
    (hψ : AnalyticAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0)
    (hd : 0 < σ * deriv (fun t => scalarGradientSlope ψ (t, p.2)) p.1) :
    0 < σ * deriv (fun t => scalarGradientAngle ψ (t, p.2)) p.1 := by
  rw [scalarGradientAngle_deriv hψ hh, ← mul_div_assoc]
  exact div_pos hd (by positivity)

/-- A fixed orientation of a slope also orients its principal angle.
This statement permits either increasing or decreasing original slices. -/
theorem scalarGradientAngle_strictMonoOn
    {ψ : ℝ × Plane → ℝ} {q : Plane} {J : Set ℝ} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hm : StrictMonoOn (fun t => σ * scalarGradientSlope ψ (t, q)) J) :
    StrictMonoOn (fun t => σ * scalarGradientAngle ψ (t, q)) J := by
  rcases hσ with rfl | rfl
  · intro a ha b hb hab
    simpa only [one_mul, scalarGradientAngle] using
      Real.arctan_strictMono (by simpa only [one_mul] using hm ha hb hab)
  · intro a ha b hb hab
    have hs : scalarGradientSlope ψ (b, q) < scalarGradientSlope ψ (a, q) := by
      simpa only [neg_one_mul, neg_lt_neg_iff] using hm ha hb hab
    simpa only [neg_one_mul, scalarGradientAngle, neg_lt_neg_iff] using
      Real.arctan_strictMono hs

/-- The principal angle represents the actual gradient line, rather than
an unrelated monotone coordinate. -/
theorem scalarGradientAngle_parallel
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hh : scalarHeadDerivative ψ p ≠ 0) :
    scalarHeadDerivative ψ p * Real.sin (scalarGradientAngle ψ p) =
      scalarTailDerivative ψ p * Real.cos (scalarGradientAngle ψ p) := by
  simp only [scalarGradientAngle, Real.sin_arctan, Real.cos_arctan,
    scalarGradientSlope]
  field_simp

private theorem sqrt_one_add_div_sq (a b : ℝ) (ha : a ≠ 0) :
    Real.sqrt (1 + (b / a) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / |a| := by
  have he : 1 + (b / a) ^ 2 = (a ^ 2 + b ^ 2) / a ^ 2 := by
    field_simp
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs]

/-- On a positive-head chart the principal angle is the actual oriented
Euclidean unit gradient. -/
theorem scalarGradientAngle_unitGradient_of_head_pos
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hh : 0 < scalarHeadDerivative ψ p) :
    (Real.cos (scalarGradientAngle ψ p), Real.sin (scalarGradientAngle ψ p)) =
      (scalarHeadDerivative ψ p /
          Real.sqrt (scalarHeadDerivative ψ p ^ 2 + scalarTailDerivative ψ p ^ 2),
       scalarTailDerivative ψ p /
          Real.sqrt (scalarHeadDerivative ψ p ^ 2 + scalarTailDerivative ψ p ^ 2)) := by
  have hs : Real.sqrt
      (1 + (scalarTailDerivative ψ p / scalarHeadDerivative ψ p) ^ 2) =
      Real.sqrt (scalarHeadDerivative ψ p ^ 2 + scalarTailDerivative ψ p ^ 2) /
        scalarHeadDerivative ψ p := by
    rw [sqrt_one_add_div_sq _ _ hh.ne', abs_of_pos hh]
  apply Prod.ext
  · simp only [scalarGradientAngle, Real.cos_arctan, scalarGradientSlope, hs]
    rw [one_div_div]
  · simp only [scalarGradientAngle, Real.sin_arctan, scalarGradientSlope, hs]
    rw [div_div_div_cancel_right₀ hh.ne']

/-- Adding π on a negative-head chart gives the actual oriented unit
gradient. This is needed when a projection theorem uses directed normals. -/
theorem scalarGradientAngle_unitGradient_of_head_neg
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hh : scalarHeadDerivative ψ p < 0) :
    (Real.cos (scalarGradientAngle ψ p + Real.pi),
      Real.sin (scalarGradientAngle ψ p + Real.pi)) =
      (scalarHeadDerivative ψ p /
          Real.sqrt (scalarHeadDerivative ψ p ^ 2 + scalarTailDerivative ψ p ^ 2),
       scalarTailDerivative ψ p /
          Real.sqrt (scalarHeadDerivative ψ p ^ 2 + scalarTailDerivative ψ p ^ 2)) := by
  have hs : Real.sqrt
      (1 + (scalarTailDerivative ψ p / scalarHeadDerivative ψ p) ^ 2) =
      Real.sqrt (scalarHeadDerivative ψ p ^ 2 + scalarTailDerivative ψ p ^ 2) /
        (-scalarHeadDerivative ψ p) := by
    rw [sqrt_one_add_div_sq _ _ hh.ne, abs_of_neg hh]
  apply Prod.ext
  · simp only [Real.cos_add_pi, scalarGradientAngle, Real.cos_arctan,
      scalarGradientSlope, hs]
    rw [one_div_div, neg_div, neg_neg]
  · simp only [Real.sin_add_pi, scalarGradientAngle, Real.sin_arctan,
      scalarGradientSlope, hs]
    field_simp [hh.ne]

/-- The local patch already constructed from nonstationarity supplies
strictly monotone, regular angle slices with continuous extension to the
entire closed product box. -/
theorem exists_scalarGradientAngle_monotone_patch
    {ψ : ℝ × Plane → ℝ} {U : Set (ℝ × Plane)} (hU : IsOpen U)
    {p : ℝ × Plane} (hp : p ∈ U) (hψ : AnalyticAt ℝ ψ p)
    (hh : scalarHeadDerivative ψ p ≠ 0)
    (hd : deriv (fun t => scalarGradientSlope ψ (t, p.2)) p.1 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      closedBall p r ⊆ U ∧
      ContinuousOn (scalarGradientAngle ψ) (closedBall p r) ∧
      (∀ z ∈ closedBall p r, scalarHeadDerivative ψ z ≠ 0 ∧
        0 < σ * deriv (fun t => scalarGradientAngle ψ (t, z.2)) z.1) ∧
      ∀ q ∈ closedBall p.2 r,
        StrictMonoOn (fun t => σ * scalarGradientAngle ψ (t, q)) (closedBall p.1 r) := by
  obtain ⟨r, hr, σ, hσ, hdom, hbox, hm⟩ :=
    exists_scalarGradientSlope_monotone_patch hU hp hψ hh hd
  refine ⟨r, hr, σ, hσ, hdom, ?_, ?_, ?_⟩
  · intro z hz
    exact (scalarGradientAngle_continuousAt (hbox z hz).1
      (hbox z hz).2.1).continuousWithinAt
  · intro z hz
    exact ⟨(hbox z hz).2.1,
      scalarGradientAngle_oriented_deriv_pos σ (hbox z hz).1
        (hbox z hz).2.1 (hbox z hz).2.2⟩
  · intro q hq
    exact scalarGradientAngle_strictMonoOn hσ (hm q hq)

end PlanarNikodym
