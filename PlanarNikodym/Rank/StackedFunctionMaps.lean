import PlanarNikodym.Rank.ConstrainedFiniteEvaluation
import PlanarNikodym.Geometry.LocalCoordinates

noncomputable section
open Set Module Submodule
namespace PlanarNikodym

def stackFunctionMaps {E X Y : Type*} [AddCommGroup E] [Module ℝ E]
    (C : E →ₗ[ℝ] (Y → ℝ)) (A : E →ₗ[ℝ] (X → ℝ)) : E →ₗ[ℝ] (Y ⊕ X → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow Y X ℝ ℝ).symm.toLinearMap.comp (C.prod A)

theorem stackFunctionMaps_finrank {E X Y : Type*} [AddCommGroup E] [Module ℝ E]
    (C : E →ₗ[ℝ] (Y → ℝ)) (A : E →ₗ[ℝ] (X → ℝ)) :
    finrank ℝ (stackFunctionMaps C A).range = finrank ℝ (C.prod A).range := by
  rw [stackFunctionMaps, LinearMap.range_comp]
  exact (LinearEquiv.sumArrowLequivProdArrow Y X ℝ ℝ).symm.finrank_map_eq _

theorem stackFunctionMaps_ker {E X Y : Type*} [AddCommGroup E] [Module ℝ E]
    (C : E →ₗ[ℝ] (Y → ℝ)) (A : E →ₗ[ℝ] (X → ℝ)) :
    (stackFunctionMaps C A).ker = C.ker ⊓ A.ker := by
  ext v
  change (LinearEquiv.sumArrowLequivProdArrow Y X ℝ ℝ).symm (C v, A v) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact Prod.mk_eq_zero

theorem finrank_constrained_stack {E X Y : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (C : E →ₗ[ℝ] (Y → ℝ)) (A : E →ₗ[ℝ] (X → ℝ)) :
    finrank ℝ (A.domRestrict C.ker).range =
      finrank ℝ (stackFunctionMaps C A).range - finrank ℝ C.range := by
  rw [stackFunctionMaps_finrank]
  exact finrank_restricted_range_eq_stacked_sub C A

end PlanarNikodym
