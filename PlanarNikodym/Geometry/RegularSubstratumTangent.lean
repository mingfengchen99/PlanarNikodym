import PlanarNikodym.Geometry.RegularStratumEquations
import PlanarNikodym.Geometry.AnalyticStratificationChartTopology

/-! Tangent inclusion for actual substrata; equality additionally follows
when their dimensions agree. No Whitney regularity is assumed. -/
noncomputable section
open Set Module
open scoped Topology
namespace PlanarNikodym

theorem AnalyticStratificationChart.range_fderiv_le_of_subset_regular
    {n : ℕ} (Q P : AnalyticStratificationChart (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hQK : Q.image ⊆ K)
    (hreg : RegularStratumEquations K Q.image Q.dim) (hP : P.image ⊆ Q.image)
    {q : Fin P.dim → ℝ} (hq : q ∈ P.source) :
    (fderiv ℝ P.map q).toLinearMap.range ≤
      (fderiv ℝ Q.map (Q.inverse (P.map q))).toLinearMap.range := by
  obtain ⟨c, F, hc, hFa, hF⟩ := hreg
  have hx := hP (mem_image_of_mem _ hq)
  have he := Q.range_fderiv_eq_ker_of_equations K hQK c F hc hFa hF
    (Q.inverse (P.map q)) (Q.inverse_mem_source hx)
  rw [Q.map_inverse hx] at he
  rw [he]
  have hz : F ∘ P.map =ᶠ[𝓝 q] fun _ => 0 := by
    filter_upwards [P.open_source.mem_nhds hq] with z hz
    exact (hF _ (hP (mem_image_of_mem _ hz))).1
  have hd := hz.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp q (hFa _ (hQK hx)).differentiableAt
    (P.analytic_map q hq).differentiableAt, fderiv_const_apply] at hd
  rintro _ ⟨v, rfl⟩
  exact congrArg (fun A : (Fin P.dim → ℝ) →L[ℝ] (Fin c → ℝ) => A v) hd

theorem AnalyticStratificationChart.center_rank_le_of_subset_regular
    {n m : ℕ} (Q P : AnalyticStratificationChart (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hQK : Q.image ⊆ K)
    (hreg : RegularStratumEquations K Q.image Q.dim) (hP : P.image ⊆ Q.image)
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    {q : Fin P.dim → ℝ} (hq : q ∈ P.source) :
    finrank ℝ (L.toLinearMap.comp (fderiv ℝ P.map q).toLinearMap).range ≤
      finrank ℝ (L.toLinearMap.comp
        (fderiv ℝ Q.map (Q.inverse (P.map q))).toLinearMap).range := by
  rw [LinearMap.range_comp, LinearMap.range_comp]
  exact Submodule.finrank_mono (Submodule.map_mono
    (Q.range_fderiv_le_of_subset_regular P K hQK hreg hP hq))

theorem AnalyticStratificationChart.range_fderiv_eq_of_subset_regular_same_dim
    {n : ℕ} (Q P : AnalyticStratificationChart (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hQK : Q.image ⊆ K)
    (hreg : RegularStratumEquations K Q.image Q.dim) (hP : P.image ⊆ Q.image)
    (hd : P.dim = Q.dim) {q : Fin P.dim → ℝ} (hq : q ∈ P.source) :
    (fderiv ℝ P.map q).toLinearMap.range =
      (fderiv ℝ Q.map (Q.inverse (P.map q))).toLinearMap.range := by
  apply Submodule.eq_of_le_of_finrank_eq
    (Q.range_fderiv_le_of_subset_regular P K hQK hreg hP hq)
  rw [LinearMap.finrank_range_of_inj (P.derivative_injective q hq),
    LinearMap.finrank_range_of_inj (Q.derivative_injective _
      (Q.inverse_mem_source (hP (mem_image_of_mem _ hq))))]
  simp only [finrank_fin_fun, hd]

end PlanarNikodym
