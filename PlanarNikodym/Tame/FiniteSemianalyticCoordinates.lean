import PlanarNikodym.Tame.DefinableContinuousImageComponents
import PlanarNikodym.Geometry.SemianalyticAnalyticSignDomains

/-! The actual finite-coordinate transport needed by parameter seeds.
No component property is lost by replacing Fin n with any finite labels. -/
noncomputable section
open Set
namespace PlanarNikodym

def ranFiniteCoordinateEquiv (ι : Type*) [Fintype ι] :
    (Fin (Fintype.card ι) → ℝ) ≃L[ℝ] (ι → ℝ) :=
  ({ toFun := fun x => x ∘ Fintype.equivFin ι
     invFun := fun x => x ∘ (Fintype.equivFin ι).symm
     left_inv := by intro x; funext i; simp
     right_inv := by intro x; funext i; simp
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } :
    (Fin (Fintype.card ι) → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toContinuousLinearEquiv

@[simp] theorem ranFiniteCoordinateEquiv_apply {ι : Type*} [Fintype ι]
    (x : Fin (Fintype.card ι) → ℝ) (i : ι) :
    ranFiniteCoordinateEquiv ι x i = x (Fintype.equivFin ι i) := rfl

/-- Bounded Boolean analytic sign sets, assuming analyticity only on their
actual closure, have finite and R_an-definable actual components for any
finite coordinate labels. -/
theorem finite_definable_components_of_analytic_signs_at_closure
    {ι : Type*} [Fintype ι] {J : Type} [Fintype J] {A : Set (ι → ℝ)}
    (f : J → (ι → ℝ) → ℝ) (hf : ∀ j, AnalyticOnNhd ℝ (f j) (closure A))
    (Q : (J → Fin 3) → Prop)
    (hA : ∀ x, x ∈ A ↔ Q (fun j => oneDimensionalSign (f j x)))
    (hb : Bornology.IsBounded A) :
    (componentDomains A).Finite ∧ ∀ x, RanDefinable (_root_.connectedComponentIn A x) := by
  let L := ranFiniteCoordinateEquiv ι
  let A₀ := L ⁻¹' A
  have he : closure A₀ = L ⁻¹' closure A := (L.toHomeomorph.preimage_closure A).symm
  have hfa (j : J) : AnalyticOnNhd ℝ (f j ∘ L) (closure A₀) := by
    intro x hx
    have hxA : L x ∈ closure A := by change x ∈ L ⁻¹' closure A; rwa [← he]
    exact (hf j (L x) hxA).comp (f := L) (L.analyticAt x)
  have hsemi : LocallySemianalytic A₀ :=
    locallySemianalytic_of_sign_description_at_closure (fun j => f j ∘ L) hfa Q (fun x => hA (L x))
  have hb₀ : Bornology.IsBounded A₀ := by
    have hb' := L.symm.lipschitz.isBounded_image hb
    change Bornology.IsBounded (L ⁻¹' A)
    have him : L.symm '' A = L ⁻¹' A := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [mem_preimage, L.apply_symm_apply] using hy
      · intro hx
        exact ⟨L x, hx, L.symm_apply_apply x⟩
    rwa [him] at hb'
  have hdef (i : ι) : RanDefinableOn (fun x => L x i) A₀ :=
    (ranDefinableFun_coordinate (Fintype.equivFin ι i)).ranDefinableOn
      (hsemi.ranDefinable_of_bounded hb₀)
  have hresult := hsemi.finite_definable_image_components hb₀ L L.continuous.continuousOn hdef
  have himage : L '' A₀ = A := by
    change L '' (L ⁻¹' A) = A
    exact L.toEquiv.image_preimage A
  rwa [himage] at hresult

end PlanarNikodym
