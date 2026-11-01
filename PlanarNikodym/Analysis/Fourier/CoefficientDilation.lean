import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Determinant

/-! Actual diagonal coefficient changes of variables, with inverse,
determinant, box image and Lebesgue change of variables. -/

noncomputable section
open Set MeasureTheory

namespace PlanarNikodym

def coefficientDilation {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, w i ≠ 0) :
    (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
  (show (Fin N → ℝ) ≃ₗ[ℝ] (Fin N → ℝ) from
    { toFun := fun x i => w i * x i
      invFun := fun x i => (w i)⁻¹ * x i
      left_inv := by intro x; ext i; simp [hw i]
      right_inv := by intro x; ext i; simp [hw i]
      map_add' := by intro x y; ext i; exact mul_add _ _ _
      map_smul' := by intro c x; ext i; change w i * (c * x i) = c * (w i * x i); ring
    }).toContinuousLinearEquiv

@[simp] theorem coefficientDilation_apply {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, w i ≠ 0)
    (x : Fin N → ℝ) (i : Fin N) : coefficientDilation w hw x i = w i * x i := rfl

@[simp] theorem coefficientDilation_symm_apply {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, w i ≠ 0)
    (x : Fin N → ℝ) (i : Fin N) : (coefficientDilation w hw).symm x i = (w i)⁻¹ * x i := rfl

theorem coefficientDilation_toLinearMap {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, w i ≠ 0) :
    (coefficientDilation w hw).toLinearMap = Matrix.toLin' (Matrix.diagonal w) := by
  ext x i
  simp only [Matrix.diagonal_toLin']
  rfl

theorem det_coefficientDilation {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, w i ≠ 0) :
    LinearMap.det (coefficientDilation w hw).toLinearMap = ∏ i, w i := by
  rw [coefficientDilation_toLinearMap, LinearMap.det_toLin', Matrix.det_diagonal]

theorem map_coefficientDilation_volume {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, w i ≠ 0) :
    Measure.map (coefficientDilation w hw) volume =
      ENNReal.ofReal (|(∏ i, w i)⁻¹|) • (volume : Measure (Fin N → ℝ)) := by
  have he : (coefficientDilation w hw : (Fin N → ℝ) → (Fin N → ℝ)) =
      Matrix.toLin' (Matrix.diagonal w) :=
    congrArg (fun L : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) => (L : _ → _))
      (coefficientDilation_toLinearMap w hw)
  rw [he, Real.map_matrix_volume_pi_eq_smul_volume_pi (by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)), Matrix.det_diagonal]

theorem integral_comp_coefficientDilation {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, w i ≠ 0)
    (F : (Fin N → ℝ) → ℂ) :
    (∫ x, F (coefficientDilation w hw x)) = |(∏ i, w i)⁻¹| • ∫ y, F y := by
  calc
    _ = ∫ y, F y ∂Measure.map (coefficientDilation w hw) volume :=
      ((coefficientDilation w hw).toHomeomorph.isClosedEmbedding.integral_map F).symm
    _ = _ := by
      rw [map_coefficientDilation_volume, integral_smul_measure,
        ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Positive weights carry a centered coordinate box exactly onto the
box whose radii are multiplied by those weights. -/
theorem coefficientDilation_image_box {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (R : Fin N → ℝ) :
    coefficientDilation w (fun i => (hw i).ne') '' {x | ∀ i, |x i| ≤ R i} =
      {y | ∀ i, |y i| ≤ w i * R i} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    simp only [coefficientDilation_apply, abs_mul, abs_of_pos (hw i)]
    exact mul_le_mul_of_nonneg_left (hx i) (hw i).le
  · intro hy
    refine ⟨(coefficientDilation w (fun i => (hw i).ne')).symm y, ?_,
      (coefficientDilation w (fun i => (hw i).ne')).apply_symm_apply y⟩
    intro i
    rw [coefficientDilation_symm_apply, abs_mul, abs_inv, abs_of_pos (hw i)]
    calc
      _ ≤ (w i)⁻¹ * (w i * R i) := mul_le_mul_of_nonneg_left (hy i) (inv_nonneg.mpr (hw i).le)
      _ = R i := by rw [← mul_assoc, inv_mul_cancel₀ (hw i).ne', one_mul]

end PlanarNikodym
