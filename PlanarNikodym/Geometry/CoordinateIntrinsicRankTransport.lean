import PlanarNikodym.Geometry.IntrinsicRankTransport
import PlanarNikodym.Cells.FamilyIntrinsicRankCover

/-! The actual intrinsic ranks in fixed linear parameter coordinates.
No ambient surjectivity of a lower-dimensional piece is assumed. -/
noncomputable section
open Set Module
namespace PlanarNikodym

theorem range_restriction_comp_equiv {E F H : Type}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup H] [Module ℝ H]
    (e : E ≃ₗ[ℝ] F) (A : F →ₗ[ℝ] H) (T : Submodule ℝ E) :
    ((A.comp e.toLinearMap).domRestrict T).range = (A.domRestrict (T.map e.toLinearMap)).range := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨⟨e v, ⟨v, v.property, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨_, ⟨v, hv, rfl⟩⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem map_tangent_inf_center_kernel {E F Z : Type}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup Z] [Module ℝ Z]
    (e : E ≃ₗ[ℝ] F) (L : F →ₗ[ℝ] Z) (T : Submodule ℝ E) :
    (T ⊓ (L.comp e.toLinearMap).ker).map e.toLinearMap = (T.map e.toLinearMap) ⊓ L.ker := by
  ext y
  constructor
  · rintro ⟨v, ⟨hv, hz⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hz⟩
  · rintro ⟨⟨v, hv, rfl⟩, hz⟩
    exact ⟨v, ⟨hv, hz⟩, rfl⟩

theorem AnalyticPiece.ranks_eq_coordinate_intrinsic {d : ℕ} {G : Family 2 d}
    (P : AnalyticPiece G) (ha : G.IsAnalytic)
    {q : Parameters 2 P.dim} (hq : q ∈ P.family.W) :
    let x := (parameterFrame d).symm (P.embed q)
    let T := (fderiv ℝ ((parameterFrame d).symm ∘ P.embed) q).toLinearMap.range
    P.family.pointRank q = finrank ℝ ((G.coordinateFunctionDerivative x).domRestrict
      (T ⊓ (parameterCenterDerivative d).toLinearMap.ker)).range ∧
    P.family.curveRank q = finrank ℝ ((G.coordinateFunctionDerivative x).domRestrict T).range := by
  let e := parameterFrame d
  let x := e.symm (P.embed q)
  let T := (fderiv ℝ (e.symm ∘ P.embed) q).toLinearMap.range
  let J := (fderiv ℝ P.embed q).toLinearMap
  let A := functionDerivative (fun (t : G.I.carrier) => G.γ t) (P.embed q)
  have hcoord : G.coordinateFunctionDerivative x = A.comp e.toLinearMap := by
    change functionDerivative (fun (t : G.I.carrier) y => G.γ t (e y)) x = _
    rw [functionDerivative_comp _ e x
      (fun t => (G.parameter_analytic ha _ (by simpa only [x, e.apply_symm_apply] using P.maps_to q hq)
        t).differentiableAt) e.differentiableAt]
    simp only [x, e.apply_symm_apply, e.fderiv]
    rfl
  have hJ : J.range = T.map e.toLinearMap := by
    rw [← LinearMap.range_comp]
    apply congrArg LinearMap.range
    apply LinearMap.ext
    intro v
    change fderiv ℝ P.embed q v = e (fderiv ℝ (e.symm ∘ P.embed) q v)
    rw [fderiv_comp q e.symm.differentiableAt (P.analytic_embed q hq).differentiableAt,
      e.symm.fderiv]
    exact (e.apply_symm_apply _).symm
  have hp := P.ranks_eq_intrinsic ha q hq J.range rfl
  change P.family.pointRank q = finrank ℝ (A.domRestrict
    (J.range ⊓ (LinearMap.fst ℝ (Base 2) (Aux d)).ker)).range ∧
    P.family.curveRank q = finrank ℝ (A.domRestrict J.range).range at hp
  change P.family.pointRank q = finrank ℝ ((G.coordinateFunctionDerivative x).domRestrict
    (T ⊓ (parameterCenterDerivative d).toLinearMap.ker)).range ∧
    P.family.curveRank q = finrank ℝ ((G.coordinateFunctionDerivative x).domRestrict T).range
  rw [hcoord]
  rw [range_restriction_comp_equiv e.toLinearEquiv A,
    range_restriction_comp_equiv e.toLinearEquiv A]
  have he := map_tangent_inf_center_kernel e.toLinearEquiv
    (LinearMap.fst ℝ (Base 2) (Aux d)) T
  change (T ⊓ (parameterCenterDerivative d).toLinearMap.ker).map e.toLinearMap =
    T.map e.toLinearMap ⊓ (LinearMap.fst ℝ (Base 2) (Aux d)).ker at he
  rw [he, ← hJ]
  exact hp

end PlanarNikodym
