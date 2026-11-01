import PlanarNikodym.Rank.StackedFunctionMaps

/-! Appending an actual scalar differential raises constraint rank
exactly when it detects a vector in the original constraint kernel. -/
noncomputable section
open Module
namespace PlanarNikodym

theorem finrank_prod_eq_of_ker_le {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H] [Module ℝ H]
    (C : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] H) (h : C.ker ≤ A.ker) :
    finrank ℝ (C.prod A).range = finrank ℝ C.range := by
  have he : A.domRestrict C.ker = 0 := by
    ext v
    exact h v.property
  have hr := finrank_restricted_range_add_constraint_rank C A
  rw [he, LinearMap.range_zero, finrank_bot, zero_add] at hr
  exact hr.symm

theorem finrank_prod_lt_of_kernel_witness {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H] [Module ℝ H]
    (C : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] H)
    {v : E} (hv : C v = 0) (ha : A v ≠ 0) :
    finrank ℝ C.range < finrank ℝ (C.prod A).range := by
  have hne : (A.domRestrict C.ker).range ≠ ⊥ := by
    intro he
    have hm : A v ∈ (A.domRestrict C.ker).range := ⟨⟨v, hv⟩, rfl⟩
    rw [he, Submodule.mem_bot] at hm
    exact ha hm
  have hp := Submodule.one_le_finrank_iff.mpr hne
  have hr := finrank_restricted_range_add_constraint_rank C A
  omega

end PlanarNikodym
