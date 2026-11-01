import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section
open Set Function Submodule Module
open scoped Matrix
namespace PlanarNikodym

/-- Independent functions admit a nonsingular finite evaluation matrix.
No topology, regularity, or nonemptiness of `X` is required (also handles m=0). -/
theorem exists_eval_det_ne_zero {X : Type*} {m : ℕ} (f : Fin m → X → ℝ)
    (hf : LinearIndependent ℝ f) :
    ∃ x : Fin m → X, Matrix.det (fun i j => f j (x i)) ≠ 0 := by
  classical
  have hs : (⊤ : Submodule ℝ (Fin m → ℝ)) ≤ span ℝ (range (flip f)) :=
    (span_flip_eq_top_iff_linearIndependent.mpr hf).ge
  let ι := (linearIndepOn_empty ℝ (id : (Fin m → ℝ) → (Fin m → ℝ))).extend
    (empty_subset (range (flip f)))
  let b : Basis ι ℝ (Fin m → ℝ) := Basis.ofSpan hs
  letI : Finite ι := b.linearIndependent.finite
  letI : Fintype ι := Fintype.ofFinite ι
  have hc : Fintype.card ι = Fintype.card (Fin m) := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_pi]
  let e := Fintype.equivOfCardEq hc
  let b' := b.reindex e
  have hb : ∀ i, ∃ x, flip f x = b' i := by
    intro i
    apply Basis.ofSpan_subset hs
    exact ⟨e.symm i, (b.reindex_apply e i).symm⟩
  choose x hx using hb
  refine ⟨x, ?_⟩
  have hrow : (fun i j => f j (x i)) = b' := by
    funext i j
    exact congrFun (hx i) j
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  simpa only [Matrix.row, hrow] using b'.linearIndependent

/-- A nonsingular evaluation matrix also certifies independence. -/
theorem independent_of_eval_det_ne_zero {X : Type*} {m : ℕ}
    (f : Fin m → X → ℝ) (x : Fin m → X)
    (h : Matrix.det (fun i j => f j (x i)) ≠ 0) : LinearIndependent ℝ f := by
  classical
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j => f j (x i)
  have hA : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hz : A *ᵥ c = A *ᵥ 0 := by
    ext i
    have ht := congrFun hc (x i)
    simpa [A, Matrix.mulVec, dotProduct, Finset.sum_apply, smul_eq_mul, mul_comm] using ht
  intro i
  exact congrFun (hA hz) i

end PlanarNikodym
