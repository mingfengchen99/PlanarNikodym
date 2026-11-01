import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Exact determinant and dual-coordinate changes for the actual Fourier
integral. These identities retain the full affine frequency center. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def glyzAdjointEquiv (L : E ≃L[ℝ] E) : E ≃L[ℝ] E :=
  (show E ≃ₗ[ℝ] E from
    { toFun := L.toContinuousLinearMap.adjoint
      invFun := L.symm.toContinuousLinearMap.adjoint
      left_inv := by
        intro x
        have h : L.toContinuousLinearMap.comp L.symm.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by ext y; simp
        have hh := congrArg ContinuousLinearMap.adjoint h
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hh
        exact congrArg (fun A : E →L[ℝ] E => A x) hh
      right_inv := by
        intro x
        have h : L.symm.toContinuousLinearMap.comp L.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by ext y; simp
        have hh := congrArg ContinuousLinearMap.adjoint h
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hh
        exact congrArg (fun A : E →L[ℝ] E => A x) hh
      map_add' := map_add _
      map_smul' := by intro c x; exact map_smul _ c x }).toContinuousLinearEquiv

theorem glyzAdjointEquiv_inner (L : E ≃L[ℝ] E) (x ξ : E) :
    inner ℝ (glyzAdjointEquiv L x) ξ = inner ℝ x (L ξ) :=
  L.toContinuousLinearMap.adjoint_inner_left ξ x

theorem det_glyzAdjointEquiv (L : E ≃L[ℝ] E) :
    LinearMap.det (glyzAdjointEquiv L).toLinearMap = LinearMap.det L.toLinearMap := by
  let b := stdOrthonormalBasis ℝ E
  change LinearMap.det (LinearMap.adjoint L.toLinearMap) = _
  rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
    Matrix.det_conjTranspose, star_trivial, LinearMap.det_toMatrix]

variable [MeasurableSpace E] [BorelSpace E]

theorem glyz_fourierInv_eq_integral_char (f : E → ℂ) (x : E) :
    𝓕⁻ f x = ∫ ξ, (Real.fourierChar (inner ℝ x ξ) : ℂ) * f ξ := by
  rw [Real.fourierInv_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    change Real.fourierChar (inner ℝ ξ x) • f ξ =
      (Real.fourierChar (inner ℝ x ξ) : ℂ) * f ξ
    rw [real_inner_comm ξ x, Circle.smul_def, smul_eq_mul]

theorem glyz_integral_comp_linearEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E ≃L[ℝ] E) (f : E → F) :
    (∫ x, f (L x)) = |(LinearMap.det L.toLinearMap)⁻¹| • ∫ x, f x := by
  calc
    _ = ∫ x, f x ∂Measure.map L volume :=
      (L.toHomeomorph.isClosedEmbedding.integral_map f).symm
    _ = _ := by
      rw [show Measure.map L volume =
        ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| • volume from
        Measure.map_linearMap_addHaar_eq_smul_addHaar volume
          (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero,
        integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- An affine frequency change becomes modulation, a determinant density,
and the actual dual linear change on physical space. No Fourier support
or decoupling estimate is assumed in this identity. -/
theorem glyz_fourierInv_affine (L : E ≃L[ℝ] E) (a : E) (f : E → ℂ) (x : E) :
    𝓕⁻ (fun ξ => f (L.symm (ξ - a))) x =
      (Real.fourierChar (inner ℝ x a) : ℂ) *
        (|LinearMap.det L.toLinearMap| • 𝓕⁻ f (glyzAdjointEquiv L x)) := by
  have hd : LinearMap.det L.toLinearMap ≠ 0 := (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  have hi : 𝓕⁻ (fun ξ => f (L.symm (ξ - a))) x =
      ∫ ξ, (Real.fourierChar (inner ℝ x ξ) : ℂ) * f (L.symm (ξ - a)) :=
    glyz_fourierInv_eq_integral_char _ _
  rw [hi]
  let H : E → ℂ := fun ξ => (Real.fourierChar (inner ℝ x ξ) : ℂ) * f (L.symm (ξ - a))
  have hc := glyz_integral_comp_linearEquiv L (fun ξ => H (ξ + a))
  have ht : (∫ ξ, H (ξ + a)) = ∫ ξ, H ξ := integral_add_right_eq_self H a
  have he : (∫ ξ, H (L ξ + a)) =
      (Real.fourierChar (inner ℝ x a) : ℂ) * 𝓕⁻ f (glyzAdjointEquiv L x) := by
    rw [glyz_fourierInv_eq_integral_char, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by
      dsimp only [H]
      rw [add_sub_cancel_right, L.symm_apply_apply, inner_add_right,
        Real.fourierChar.map_add_eq_mul, Circle.coe_mul, ← glyzAdjointEquiv_inner L x ξ]
      ring
  rw [he, ht] at hc
  have he' := congrArg (fun z : ℂ => |LinearMap.det L.toLinearMap| • z) hc
  rw [smul_smul, ← abs_mul, mul_inv_cancel₀ hd, abs_one, one_smul] at he'
  change (∫ ξ, H ξ) = _
  rw [← he']
  simp only [Complex.real_smul]
  ring

end PlanarNikodym
