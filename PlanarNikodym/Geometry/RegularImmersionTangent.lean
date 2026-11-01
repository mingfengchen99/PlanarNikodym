import PlanarNikodym.Geometry.RegularSubstratumTangent

/-! An actual immersion of the same dimension into a regular stratum
has precisely its tangent range. The source may be any finite-dimensional
normed space, including a center/auxiliary product. -/
noncomputable section
open Set Filter Module
open scoped Topology
namespace PlanarNikodym

theorem AnalyticStratificationChart.range_fderiv_eq_of_immersion_subset
    {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : AnalyticStratificationChart (Fin n → ℝ)) (K : Set (Fin n → ℝ))
    (hQK : Q.image ⊆ K) (hreg : RegularStratumEquations K Q.image Q.dim)
    (φ : E → (Fin n → ℝ)) {V : Set E} (hV : IsOpen V)
    (ha : AnalyticOnNhd ℝ φ V) (hsub : φ '' V ⊆ Q.image)
    (hd : finrank ℝ E = Q.dim) {q : E} (hq : q ∈ V)
    (hi : Function.Injective (fderiv ℝ φ q)) :
    (fderiv ℝ φ q).toLinearMap.range =
      (fderiv ℝ Q.map (Q.inverse (φ q))).toLinearMap.range := by
  obtain ⟨c, F, hc, hFa, hF⟩ := hreg
  have hx := hsub (mem_image_of_mem _ hq)
  have hT := Q.range_fderiv_eq_ker_of_equations K hQK c F hc hFa hF
    (Q.inverse (φ q)) (Q.inverse_mem_source hx)
  rw [Q.map_inverse hx] at hT
  have hzero : F ∘ φ =ᶠ[𝓝 q] fun _ => 0 := by
    filter_upwards [hV.mem_nhds hq] with z hz
    exact (hF _ (hsub (mem_image_of_mem _ hz))).1
  have hD := hzero.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp q (hFa _ (hQK hx)).differentiableAt (ha q hq).differentiableAt,
    fderiv_const_apply] at hD
  have hle : (fderiv ℝ φ q).toLinearMap.range ≤ (fderiv ℝ F (φ q)).toLinearMap.ker := by
    rintro _ ⟨v, rfl⟩
    exact congrArg (fun D : E →L[ℝ] (Fin c → ℝ) => D v) hD
  apply Submodule.eq_of_le_of_finrank_eq (by rwa [hT])
  rw [LinearMap.finrank_range_of_inj hi, hd,
    LinearMap.finrank_range_of_inj (Q.derivative_injective _ (Q.inverse_mem_source hx)),
    finrank_fin_fun]

end PlanarNikodym
