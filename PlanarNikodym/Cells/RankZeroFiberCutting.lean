import PlanarNikodym.Rank.FiniteIntrinsicRankCover
import PlanarNikodym.Cells.LowDimensionalProjectionContainer

/-! Actual fiber cutting of a zero-center-rank stratum, in arbitrary
source dimension. Connectedness makes its center image one point. -/
noncomputable section
open Set Module
namespace PlanarNikodym

theorem AnalyticStratificationChart.same_projection_singleton_of_rank_zero
    {n m : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (hr : ∀ q ∈ Q.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = 0) :
    ∃ x ∈ Q.image, L '' ({x} : Set (Fin n → ℝ)) = L '' Q.image := by
  have ha : AnalyticOnNhd ℝ (L ∘ Q.map) Q.source :=
    fun q hq => (L.analyticAt _).comp (Q.analytic_map q hq)
  have hz : ∀ q ∈ Q.source, fderiv ℝ (L ∘ Q.map) q = 0 := by
    intro q hq
    rw [fderiv_comp q L.differentiableAt (Q.analytic_map q hq).differentiableAt,
      L.fderiv]
    have he := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (hr q hq))
    ext v i
    exact congrFun (LinearMap.congr_fun he v) i
  obtain ⟨q, hq⟩ := Q.connected_source.nonempty
  refine ⟨Q.map q, mem_image_of_mem _ hq, ?_⟩
  rw [image_singleton]
  ext y
  constructor
  · intro hy
    rw [mem_singleton_iff] at hy
    exact hy ▸ mem_image_of_mem L (mem_image_of_mem _ hq)
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact Q.open_source.is_const_of_fderiv_eq_zero Q.connected_source.isPreconnected
      ha.differentiableOn hz hp hq

theorem AnalyticStratificationChart.exists_semianalytic_rank_zero_fiber_cut
    {n m : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (hr : ∀ q ∈ Q.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = 0) :
    ∃ B : Set (Fin n → ℝ), B ⊆ Q.image ∧ LocallySemianalytic B ∧
      Bornology.IsBounded B ∧ dimH B = 0 ∧ L '' B = L '' Q.image := by
  obtain ⟨x, hx, he⟩ := Q.same_projection_singleton_of_rank_zero L hr
  refine ⟨{x}, singleton_subset_iff.mpr hx, ?_, Bornology.isBounded_singleton,
    dimH_singleton _, he⟩
  have he : ({x} : Set (Fin n → ℝ)) = ⋂ i : Fin n, {y | y i - x i = 0} := by
    ext y
    simp only [mem_singleton_iff, mem_iInter, mem_setOf_eq, sub_eq_zero]
    exact funext_iff
  rw [he]
  exact LocallySemianalytic.iInter _ (fun i =>
    locallySemianalytic_global_analytic_zero_set _
      (fun y => (analyticAt_coordinate i y).sub analyticAt_const))

end PlanarNikodym
