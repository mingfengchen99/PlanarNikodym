import PlanarNikodym.Rank.FiniteEvaluation

/-! A nonsingular matrix supplies a genuine nonsingular coordinate
minor for each initial segment of its rows. -/

noncomputable section
open Function
open scoped Matrix

namespace PlanarNikodym

theorem exists_initial_coordinate_minor {N m : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.det ≠ 0) (hm : m ≤ N) :
    ∃ σ : Fin m ↪ Fin N,
      Matrix.det (fun i j : Fin m => A (Fin.castLE hm i) (σ j)) ≠ 0 := by
  have hli : LinearIndependent ℝ (fun i => A i) := by
    exact Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))
  have hinit : LinearIndependent ℝ (fun i : Fin m => A (Fin.castLE hm i)) :=
    hli.comp (Fin.castLE hm) (Fin.castLE_injective hm)
  obtain ⟨σ, hσ⟩ := exists_eval_det_ne_zero (fun i : Fin m => A (Fin.castLE hm i)) hinit
  have hinj : Injective σ := by
    intro i j hij
    by_contra hne
    apply hσ
    apply Matrix.det_zero_of_row_eq hne
    funext k
    exact congrArg (fun z => A (Fin.castLE hm k) z) hij
  refine ⟨⟨σ, hinj⟩, ?_⟩
  change Matrix.det (fun i j : Fin m => A (Fin.castLE hm i) (σ j)) ≠ 0
  have he : (fun i j : Fin m => A (Fin.castLE hm i) (σ j)) =
      (fun i j : Fin m => A (Fin.castLE hm j) (σ i))ᵀ := rfl
  rw [he, Matrix.det_transpose]
  exact hσ

end PlanarNikodym
