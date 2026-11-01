import PlanarNikodym.Rank.IntrinsicRankRefinement
import PlanarNikodym.Rank.ScalarConstraintRank

/-! A single actual ambient minor contains every fiber critical point.
The minor is nontrivial on the connected stratum, since a specified
vertical tangent is detected by the appended scalar differential. -/
noncomputable section
open Set Module
namespace PlanarNikodym

theorem AnalyticStratificationChart.exists_fiber_critical_minor
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hQK : Q.image ⊆ K)
    (hreg : RegularStratumEquations K Q.image Q.dim)
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) (r : ℕ)
    (hr : ∀ q ∈ Q.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = r)
    (g : (Fin n → ℝ) → ℝ) (hg : AnalyticOnNhd ℝ g K)
    {x : Fin n → ℝ} (hx : x ∈ Q.image) {v : Fin n → ℝ}
    (hvT : v ∈ (fderiv ℝ Q.map (Q.inverse x)).toLinearMap.range)
    (hvL : L v = 0) (hvg : fderiv ℝ g x v ≠ 0) :
    ∃ h : (Fin n → ℝ) → ℝ, AnalyticOnNhd ℝ h K ∧
      Q.image ⊆ closure {z | z ∈ Q.image ∧ h z ≠ 0} ∧
      ∀ z ∈ Q.image,
        (∀ w ∈ (fderiv ℝ Q.map (Q.inverse z)).toLinearMap.range,
          L w = 0 → fderiv ℝ g z w = 0) → h z = 0 := by
  obtain ⟨c, F, hc, hFa, hF⟩ := hreg
  let C (z : Fin n → ℝ) := (fderiv ℝ F z).toLinearMap
  let H (z : Fin n → ℝ) := stackFunctionMaps (C z) L.toLinearMap
  let D (z : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
    LinearMap.pi (fun _ => (fderiv ℝ g z).toLinearMap)
  let B (z : Fin n → ℝ) := stackFunctionMaps (H z) (D z)
  have hT (z : Fin n → ℝ) (hz : z ∈ Q.image) :
      (fderiv ℝ Q.map (Q.inverse z)).toLinearMap.range = (C z).ker := by
    have he := Q.range_fderiv_eq_ker_of_equations K hQK c F hc hFa hF
      (Q.inverse z) (Q.inverse_mem_source hz)
    simpa only [Q.map_inverse hz] using he
  have hHrank (z : Fin n → ℝ) (hz : z ∈ Q.image) : finrank ℝ (H z).range = c + r := by
    have hCrank : finrank ℝ (C z).range = c := by
      rw [LinearMap.range_eq_top.mpr (hF z hz).2, finrank_top, finrank_fin_fun]
    have hLrank : finrank ℝ (L.toLinearMap.domRestrict (C z).ker).range = r := by
      rw [← range_comp_eq_map_of_range_eq L.toLinearMap _ _ (hT z hz)]
      exact hr _ (Q.inverse_mem_source hz)
    have he := finrank_restricted_range_add_constraint_rank (C z) L.toLinearMap
    rw [hCrank, hLrank, ← stackFunctionMaps_finrank] at he
    exact he.symm.trans (Nat.add_comm r c)
  have hBa (j : Fin n) (t : (Fin c ⊕ Fin 2) ⊕ Fin 1) :
      AnalyticOnNhd ℝ (fun z => B z (Pi.single j 1) t) K := by
    rcases t with (t | t) | t
    · intro z hz
      exact ((ContinuousLinearMap.proj t).analyticAt _).comp
        (((ContinuousLinearMap.apply ℝ (Fin c → ℝ) (Pi.single j 1)).analyticAt _).comp
          (hFa z hz).fderiv)
    · exact analyticOnNhd_const
    · intro z hz
      exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)).analyticAt _).comp (hg z hz).fderiv
  obtain ⟨M, _, hMa, _, hdense, hmax, heq⟩ := Q.generic_ambient_evaluation_minor K hQK
    (fun j t z => B z (Pi.single j 1) t) hBa
  have hMv : c + r < M.size := by
    have hvH : H x v = 0 := by
      have hvCm : v ∈ (C x).ker := (hT x hx) ▸ hvT
      have hvC : C x v = 0 := hvCm
      change (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm (C x v, L v) = 0
      rw [hvC, hvL]
      exact map_zero _
    have hvD : D x v ≠ 0 := by
      intro he
      exact hvg (congrFun he 0)
    have hl := finrank_prod_lt_of_kernel_witness (H x) (D x) hvH hvD
    rw [← stackFunctionMaps_finrank, hHrank x hx] at hl
    have hm := hmax x hx
    rw [← range_eq_span_coordinates (B x)] at hm
    exact hl.trans_le hm
  refine ⟨M.value (fun j t z => B z (Pi.single j 1) t), hMa, hdense, ?_⟩
  intro z hz hcrit
  by_contra hn
  have hker : (H z).ker ≤ (D z).ker := by
    intro w hw
    have hw' : w ∈ (C z).ker ⊓ L.toLinearMap.ker := by
      rwa [stackFunctionMaps_ker] at hw
    have he := hcrit w ((hT z hz).symm ▸ hw'.1) hw'.2
    change (fun _ : Fin 1 => fderiv ℝ g z w) = 0
    exact funext (fun _ => he)
  have hb := finrank_prod_eq_of_ker_le (H z) (D z) hker
  rw [← stackFunctionMaps_finrank, hHrank z hz] at hb
  have hm := heq z hz hn
  rw [← range_eq_span_coordinates (B z)] at hm
  have he : M.size = c + r := hm.symm.trans hb
  omega

end PlanarNikodym
