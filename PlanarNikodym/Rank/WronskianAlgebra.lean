import PlanarNikodym.Geometry.Cinematic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
open Set Filter Submodule
open scoped Topology Matrix
namespace PlanarNikodym

theorem analyticAt_iteratedDeriv_real {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (k : ℕ) : AnalyticAt ℝ (iteratedDeriv k f) x := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).analyticAt _).comp ih.fderiv

theorem wronskian_analytic {n : ℕ} (f : Fin n → ℝ → ℝ) (S : Set ℝ)
    (hf : ∀ j, AnalyticOnNhd ℝ (f j) S) : AnalyticOnNhd ℝ (wronskian f) S := by
  intro x hx
  exact analyticAt_det (fun i j => analyticAt_iteratedDeriv_real (hf j x hx) i)

/-- In a singular bordered matrix, an invertible initial square minor
forces the last column into the span of the preceding columns. -/
theorem last_column_mem_span_of_singular {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hminor : Matrix.det (fun i j : Fin n => A i.castSucc j.castSucc) ≠ 0)
    (hdet : A.det = 0) :
    (fun i => A i (Fin.last n)) ∈
      span ℝ (range (fun j : Fin n => fun i => A i j.castSucc)) := by
  classical
  have hli : LinearIndependent ℝ (fun j : Fin n => fun i => A i j.castSucc) :=
    independent_of_eval_det_ne_zero _ (fun i => i.castSucc) hminor
  by_contra hn
  have hfull : LinearIndependent ℝ A.col :=
    linearIndependent_finSucc'.mpr ⟨hli, hn⟩
  have hunit : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hfull)
  exact (isUnit_iff_ne_zero.mp hunit) hdet

/-- An invertible Wronskian minor kills a coefficient derivative vector.
The coefficients are scalar functions; the derivative is an actual deriv. -/
theorem coefficient_derivatives_zero {n : ℕ} (f : Fin n → ℝ → ℝ)
    (C : Fin n → ℝ → ℝ) (x : ℝ) (hW : wronskian f x ≠ 0)
    (h : ∀ i : Fin n, ∑ j, deriv (C j) x * iteratedDeriv i (f j) x = 0) :
    ∀ j, deriv (C j) x = 0 := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => iteratedDeriv i (f j) x
  have hi : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hW))
  have hz : A *ᵥ (fun j => deriv (C j) x) = A *ᵥ 0 := by
    ext i
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using h i
  exact fun j => congrFun (hi hz) j

end PlanarNikodym
