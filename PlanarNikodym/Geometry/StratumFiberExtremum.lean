import PlanarNikodym.Geometry.RankOneFiberExtremum
import PlanarNikodym.Rank.IntrinsicRankRefinement

/-! Fiber extrema on an arbitrary actual stratum. This works on open
restrictions of the source, so artificial compact windows do not require
the stratum parametrization to extend analytically to its closure. -/
noncomputable section
open Set Module
namespace PlanarNikodym

theorem AnalyticStratificationChart.rank_one_fiber_extremum
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (hr : ∀ q ∈ Q.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = 1)
    {U V : Set (Fin n → ℝ)} (hQU : Q.image ⊆ U)
    (g : (Fin n → ℝ) → ℝ) (hg : AnalyticOnNhd ℝ g U)
    (hV : IsOpen V) {y : Fin n → ℝ} (hy : y ∈ Q.image ∩ V)
    (hm : IsMaxOn g {z | z ∈ Q.image ∩ V ∧ L z = L y} y)
    {v : Fin n → ℝ}
    (hvT : v ∈ (fderiv ℝ Q.map (Q.inverse y)).toLinearMap.range)
    (hvL : L v = 0) : fderiv ℝ g y v = 0 := by
  let C := L ∘ Q.map
  let H := g ∘ Q.map
  let S := Q.source ∩ Q.map ⁻¹' V
  have hS : IsOpen S := Q.analytic_map.continuousOn.isOpen_inter_preimage Q.open_source hV
  have hCa : AnalyticOnNhd ℝ C S := fun q hq =>
    (L.analyticAt _).comp (Q.analytic_map q hq.1)
  have hHa : AnalyticOnNhd ℝ H S := fun q hq =>
    (hg _ (hQU (mem_image_of_mem _ hq.1))).comp (Q.analytic_map q hq.1)
  have hCd (q : Fin Q.dim → ℝ) (hq : q ∈ Q.source) :
      fderiv ℝ C q = L.comp (fderiv ℝ Q.map q) := by
    rw [fderiv_comp q L.differentiableAt (Q.analytic_map q hq).differentiableAt, L.fderiv]
  have hns (q : Fin Q.dim → ℝ) (hq : q ∈ S) :
      ¬ Function.Surjective (fderiv ℝ C q) := by
    intro hs
    have he := hr q hq.1
    change finrank ℝ (L.comp (fderiv ℝ Q.map q)).toLinearMap.range = 1 at he
    rw [← hCd q hq.1] at he
    have ht := LinearMap.range_eq_top.mpr hs
    rw [ht, finrank_top, finrank_fin_fun] at he
    omega
  have hq : Q.inverse y ∈ S :=
    ⟨Q.inverse_mem_source hy.1, by simpa only [mem_preimage, Q.map_inverse hy.1] using hy.2⟩
  have hnon : fderiv ℝ C (Q.inverse y) ≠ 0 := by
    intro he
    have hr' := hr _ hq.1
    have he' : L.toLinearMap.comp (fderiv ℝ Q.map (Q.inverse y)).toLinearMap = 0 := by
      change (L.comp (fderiv ℝ Q.map (Q.inverse y))).toLinearMap = 0
      rw [← hCd _ hq.1, he]
      rfl
    rw [he', LinearMap.range_zero, finrank_bot] at hr'
    omega
  have hmax : IsMaxOn H {z | z ∈ S ∧ C z = C (Q.inverse y)} (Q.inverse y) := by
    intro z hz
    change g (Q.map z) ≤ g (Q.map (Q.inverse y))
    rw [Q.map_inverse hy.1]
    exact hm ⟨⟨mem_image_of_mem _ hz.1.1, hz.1.2⟩,
      by simpa only [C, Function.comp_apply, Q.map_inverse hy.1] using hz.2⟩
  obtain ⟨w, hw⟩ := hvT
  change fderiv ℝ Q.map (Q.inverse y) w = v at hw
  have hwC : fderiv ℝ C (Q.inverse y) w = 0 := by
    rw [hCd _ hq.1]
    change L (fderiv ℝ Q.map (Q.inverse y) w) = 0
    rwa [hw]
  have he := analytic_rank_one_fiber_maximum_derivative C H hS hCa hHa hns hq hnon hmax hwC
  rw [fderiv_comp _ (hg _ (hQU (mem_image_of_mem _ hq.1))).differentiableAt
    (Q.analytic_map _ hq.1).differentiableAt, Q.map_inverse hy.1] at he
  simpa only [ContinuousLinearMap.comp_apply, hw] using he

end PlanarNikodym
