import PlanarNikodym.Rank.FiniteEvaluation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank-nullity for the actual restriction to a constraint kernel. The
stacked-map formula also applies when the second target is a function
space; no finite-dimensional target assumption is needed. -/
noncomputable section
open Set Module
namespace PlanarNikodym

theorem finrank_restricted_range_add_constraint_rank
    {E F H : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H] [Module ℝ H]
    (C : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] H) :
    finrank ℝ (A.domRestrict C.ker).range + finrank ℝ C.range =
      finrank ℝ (C.prod A).range := by
  let e : (A.domRestrict C.ker).ker ≃ₗ[ℝ] (C.prod A).ker :=
    { toFun := fun v => ⟨v.val.val, Prod.ext v.val.property v.property⟩
      invFun := fun v => ⟨⟨v.val, congrArg Prod.fst v.property⟩,
        congrArg Prod.snd v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h₁ := (A.domRestrict C.ker).finrank_range_add_finrank_ker
  have h₂ := C.finrank_range_add_finrank_ker
  have h₃ := (C.prod A).finrank_range_add_finrank_ker
  have hk := e.finrank_eq
  omega

theorem finrank_restricted_range_eq_stacked_sub
    {E F H : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H] [Module ℝ H]
    (C : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] H) :
    finrank ℝ (A.domRestrict C.ker).range =
      finrank ℝ (C.prod A).range - finrank ℝ C.range := by
  have h := finrank_restricted_range_add_constraint_rank C A
  omega

/-- A centre constraint is stacked before evaluating the point rank.
Its kernel is precisely the tangent directions with zero centre motion. -/
theorem stacked_constraint_ker {E F Z : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup Z] [Module ℝ Z] (C : E →ₗ[ℝ] F) (L : E →ₗ[ℝ] Z) :
    (C.prod L).ker = C.ker ⊓ L.ker := LinearMap.ker_prod C L

/-- Tangent transport requires surjectivity onto the tangent subspace,
not onto the original ambient parameter space. -/
theorem range_comp_eq_map_of_range_eq {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup H] [Module ℝ H] (A : F →ₗ[ℝ] H) (J : E →ₗ[ℝ] F)
    (T : Submodule ℝ F) (hJ : J.range = T) :
    (A.comp J).range = (A.domRestrict T).range := by
  rw [LinearMap.range_comp, hJ, LinearMap.range_domRestrict]

end PlanarNikodym
