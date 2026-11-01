import PlanarNikodym.Rank.ConstrainedRank

/-! Actual finite evaluation witnesses for constrained function-space
ranks. One time tuple is injective on the full derivative image and hence
works simultaneously for every tangent/vertical subspace. -/
noncomputable section
open Set Module Submodule
namespace PlanarNikodym

def finiteEvaluation {X : Type*} {m : ℕ} (t : Fin m → X) :
    (X → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.pi (fun i => LinearMap.proj (t i))

theorem exists_finiteEvaluation_injective {X : Type*}
    (V : Submodule ℝ (X → ℝ)) [FiniteDimensional ℝ V] :
    ∃ t : Fin (finrank ℝ V) → X,
      Function.Injective ((finiteEvaluation t).domRestrict V) := by
  classical
  let b := Module.finBasis ℝ V
  have hli : LinearIndependent ℝ (fun i => (b i).val) :=
    b.linearIndependent.map' V.subtype (LinearMap.ker_eq_bot.mpr V.subtype_injective)
  obtain ⟨t, ht⟩ := exists_eval_det_ne_zero (fun i => (b i).val) hli
  refine ⟨t, LinearMap.injective_of_linearIndependent b.span_eq ?_⟩
  have hM := (Matrix.linearIndependent_cols_iff_isUnit
    (A := fun i j => (b j).val (t i))).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht))
  change LinearIndependent ℝ (fun j i => (b j).val (t i))
  exact hM

theorem finrank_ranges_eq_of_ker_eq
    {E F H : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H] [Module ℝ H]
    (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] H) (he : A.ker = B.ker) :
    finrank ℝ A.range = finrank ℝ B.range := by
  have hA := A.finrank_range_add_finrank_ker
  have hB := B.finrank_range_add_finrank_ker
  rw [he] at hA
  omega

theorem evaluated_restriction_ker_eq {E X : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (A : E →ₗ[ℝ] (X → ℝ)) (t : Fin m → X)
    (hi : Function.Injective ((finiteEvaluation t).domRestrict A.range))
    (T : Submodule ℝ E) :
    ((finiteEvaluation t).comp (A.domRestrict T)).ker = (A.domRestrict T).ker := by
  ext v
  constructor
  · intro hv
    have he : ((finiteEvaluation t).domRestrict A.range) ⟨A v.val, ⟨v.val, rfl⟩⟩ =
        ((finiteEvaluation t).domRestrict A.range) 0 := by
      simpa only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.domRestrict_apply,
        map_zero] using hv
    exact congrArg Subtype.val (hi he)
  · intro hv
    change finiteEvaluation t (A v.val) = 0
    rw [show A v.val = 0 from hv, map_zero]

/-- A single finite time tuple preserves the rank on every source
subspace, including both ker DF and ker DF ∩ ker L. -/
theorem exists_finiteEvaluation_all_restricted_ranks {E X : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] (X → ℝ)) :
    ∃ t : Fin (finrank ℝ A.range) → X, ∀ T : Submodule ℝ E,
      finrank ℝ ((finiteEvaluation t).comp (A.domRestrict T)).range =
        finrank ℝ (A.domRestrict T).range := by
  obtain ⟨t, ht⟩ := exists_finiteEvaluation_injective A.range
  exact ⟨t, fun T => finrank_ranges_eq_of_ker_eq _ _
    (evaluated_restriction_ker_eq A t ht T)⟩

/-- After choosing actual evaluation times, the constrained function rank
is exactly the difference of two finite stacked-map ranks. -/
theorem exists_finiteEvaluation_stacked_rank_formulas {E F Z X : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup Z] [Module ℝ Z]
    (C : E →ₗ[ℝ] F) (L : E →ₗ[ℝ] Z) (A : E →ₗ[ℝ] (X → ℝ)) :
    ∃ t : Fin (finrank ℝ A.range) → X,
      finrank ℝ (A.domRestrict C.ker).range =
        finrank ℝ (C.prod ((finiteEvaluation t).comp A)).range - finrank ℝ C.range ∧
      finrank ℝ (A.domRestrict (C.ker ⊓ L.ker)).range =
        finrank ℝ ((C.prod L).prod ((finiteEvaluation t).comp A)).range -
          finrank ℝ (C.prod L).range := by
  obtain ⟨t, ht⟩ := exists_finiteEvaluation_all_restricted_ranks A
  refine ⟨t, ?_, ?_⟩
  · rw [← ht C.ker]
    exact finrank_restricted_range_eq_stacked_sub C ((finiteEvaluation t).comp A)
  · rw [← stacked_constraint_ker C L, ← ht (C.prod L).ker]
    exact finrank_restricted_range_eq_stacked_sub (C.prod L) ((finiteEvaluation t).comp A)

end PlanarNikodym
