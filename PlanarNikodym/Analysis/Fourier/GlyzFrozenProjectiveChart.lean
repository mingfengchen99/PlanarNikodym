import PlanarNikodym.Analysis.Fourier.GlyzFrozenProjectiveCurve
import PlanarNikodym.Analysis.Fourier.GlyzUniformProjectiveChart
import PlanarNikodym.Analysis.Fourier.FrozenFrequencyRepresentation

/-! The projective chart applied to the actual frozen spatial gradient.
The determinant assumption is the original time-jet parameter minor;
the Fourier normalization is retained exactly. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace PlanarNikodym

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiff_joint_glyzFrozenDirectionalCurve (k : ℕ) (Φ : P × ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (v : Fin (k + 1) → P) :
    ContDiff ℝ ∞ (fun z : P × ℝ => glyzFrozenDirectionalCurve k Φ v z.1 z.2) := by
  apply (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  exact (hΦ.fderiv_right (by simp : ∞ + 1 ≤ ∞)).clm_apply
    (contDiff_const (c := (v j, 0)))

/-- A genuine nonzero phase minor produces one uniform chart on a
parameter-time neighborhood, including all finite derivative bounds. -/
theorem exists_uniform_glyz_frozen_projective_chart [FiniteDimensional ℝ P]
    (k M : ℕ) (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (v : Fin (k + 1) → P) (w : P) (s : ℝ)
    (hdet : (timeJetParameterMatrix Φ (k + 1) v s w).det ≠ 0) :
    ∃ (A : GlyzConeSpace k ≃L[ℝ] GlyzSpace (k + 1)) (a : P × ℝ → ℝ)
      (γ : P × ℝ → GlyzSpace k) (ρ B : ℝ),
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ γ ∧ 0 < ρ ∧ 0 < B ∧
      (∀ z, 1 / 2 < a z) ∧
      (∀ z ∈ closedBall (w, s) ρ, a z ≤ B) ∧
      (∀ z ∈ closedBall (w, s) ρ,
        glyzFrozenDirectionalCurve k Φ v z.1 z.2 = A (WithLp.toLp 2 (a z • γ z, a z))) ∧
      (∀ z ∈ closedBall (w, s) ρ,
        1 / 2 ≤ |(glyzCurveJetOperator (fun t => γ (z.1, t)) z.2).det|) ∧
      (∀ z ∈ closedBall (w, s) ρ, ∀ j ≤ M,
        ‖iteratedDeriv j (fun t => γ (z.1, t)) z.2‖ ≤ B) := by
  apply exists_uniform_glyz_projective_chart k M
    (fun z : P × ℝ => glyzFrozenDirectionalCurve k Φ v z.1 z.2)
    (contDiff_joint_glyzFrozenDirectionalCurve k Φ hΦ v) w s
  rwa [det_glyzFrozenDirectionalCurve_fullJet k Φ hΦ v w s]

/-- In orthonormal Euclidean coordinates the directional curve is
exactly the Riesz representative of the spatial differential. -/
theorem glyzFrozenDirectionalCurve_basis_eq_gradient (k : ℕ)
    (Φ : GlyzSpace (k + 1) × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (w : GlyzSpace (k + 1)) (t : ℝ) :
    glyzFrozenDirectionalCurve k Φ (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) w t =
      (InnerProductSpace.toDual ℝ (GlyzSpace (k + 1))).symm
        (fderiv ℝ (fun z => Φ (z, t)) w) := by
  ext j
  conv_rhs => rw [← EuclideanSpace.inner_basisFun_real]
  rw [InnerProductSpace.toDual_symm_apply]
  rw [fderiv_fst_slice Φ (w, t) (hΦ.differentiable (by simp) (w, t))]
  rfl

/-- The localized variable extension's frequency is the actual conic
frequency of this gradient, with Mathlib's factor `2π` explicit. -/
theorem frozenSpatialFrequency_eq_glyzFrozenDirectionalCurve (k : ℕ)
    (Φ : GlyzSpace (k + 1) × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (w : GlyzSpace (k + 1)) (ρ : ℝ) (y : Plane) :
    frozenSpatialFrequency Φ w ρ y = (ρ * y.2 / (2 * Real.pi)) •
      glyzFrozenDirectionalCurve k Φ (EuclideanSpace.basisFun (Fin (k + 1)) ℝ) w y.1 := by
  rw [glyzFrozenDirectionalCurve_basis_eq_gradient k Φ hΦ]
  rfl

end PlanarNikodym
