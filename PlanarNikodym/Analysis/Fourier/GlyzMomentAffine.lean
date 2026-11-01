import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxes
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Choose.Sum

/-! The concrete parabolic affine map for Gamma(t)=(t,...,t^m).
Its linear part is built from the binomial coefficients, not assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace PlanarNikodym

def glyzMomentAffineMatrix (m : ℕ) (c κ : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (((i : ℕ) + 1).choose ((j : ℕ) + 1) : ℝ) *
    c ^ ((i : ℕ) - (j : ℕ)) * κ ^ ((j : ℕ) + 1)

theorem det_glyzMomentAffineMatrix (m : ℕ) (c κ : ℝ) :
    (glyzMomentAffineMatrix m c κ).det = ∏ j : Fin m, κ ^ ((j : ℕ) + 1) := by
  rw [Matrix.det_of_lowerTriangular _ (by
    intro i j hij
    have hij' : i < j := hij
    have h : (i : ℕ) + 1 < (j : ℕ) + 1 := by exact Nat.add_lt_add_right hij' 1
    simp [glyzMomentAffineMatrix, Nat.choose_eq_zero_of_lt h])]
  simp [glyzMomentAffineMatrix]

def glyzMomentAffineLinear (m : ℕ) (c κ : ℝ) (hκ : κ ≠ 0) : Base m ≃L[ℝ] Base m :=
  (Matrix.toLin' (glyzMomentAffineMatrix m c κ)).equivOfDetNeZero
    (by rw [LinearMap.det_toLin', det_glyzMomentAffineMatrix];
        exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ hκ)
    |>.toContinuousLinearEquiv

theorem glyzMomentAffineLinear_apply (m : ℕ) (c κ : ℝ) (hκ : κ ≠ 0) (v : Base m) :
    glyzMomentAffineLinear m c κ hκ v = (glyzMomentAffineMatrix m c κ).mulVec v := rfl

theorem glyzMomentAffineLinear_curve (m : ℕ) (c κ t : ℝ) (hκ : κ ≠ 0) :
    glyzMomentCurve m (c + κ * t) =
      glyzMomentCurve m c + glyzMomentAffineLinear m c κ hκ (glyzMomentCurve m t) := by
  ext i
  change (c + κ * t) ^ ((i : ℕ) + 1) = c ^ ((i : ℕ) + 1) +
    ∑ j : Fin m, (((i : ℕ) + 1).choose ((j : ℕ) + 1) : ℝ) *
      c ^ ((i : ℕ) - (j : ℕ)) * κ ^ ((j : ℕ) + 1) * t ^ ((j : ℕ) + 1)
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (((i : ℕ) + 1).choose (j + 1) : ℝ) *
    c ^ ((i : ℕ) - j) * κ ^ (j + 1) * t ^ (j + 1)) m]
  have he : (∑ j ∈ Finset.range m, (((i : ℕ) + 1).choose (j + 1) : ℝ) *
      c ^ ((i : ℕ) - j) * κ ^ (j + 1) * t ^ (j + 1)) =
      ∑ j ∈ Finset.range ((i : ℕ) + 1), (((i : ℕ) + 1).choose (j + 1) : ℝ) *
        c ^ ((i : ℕ) - j) * κ ^ (j + 1) * t ^ (j + 1) := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hj' : (i : ℕ) + 1 < j + 1 := by simp only [Finset.mem_range] at hj; omega
    simp [Nat.choose_eq_zero_of_lt hj']
  rw [he, add_comm c (κ * t), add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [add_comm (∑ j ∈ Finset.range ((i : ℕ) + 1), _) (c ^ ((i : ℕ) + 1))]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  have hj : (i : ℕ) + 1 - (j + 1) = (i : ℕ) - j := by omega
  rw [hj]
  ring

end PlanarNikodym
