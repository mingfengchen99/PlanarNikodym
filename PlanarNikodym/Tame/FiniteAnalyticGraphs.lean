import PlanarNikodym.Tame.CompactAnalyticGraphs

noncomputable section
open Set

namespace PlanarNikodym

/-- Finite coordinate labels do not change definability of analytic
patches; the primitive restricted analytic symbols still have arity `n`. -/
theorem exists_ranDefinableOn_nhds_of_compact_finite {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hf : AnalyticOnNhd ℝ f K) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧ K ⊆ U ∧
      RanDefinable U ∧ RanDefinableOn f U := by
  let e := Fintype.equivFin ι
  let L : (Fin (Fintype.card ι) → ℝ) ≃L[ℝ] (ι → ℝ) :=
    ({ toFun := fun x => x ∘ e
       invFun := fun x => x ∘ e.symm
       left_inv := by intro x; funext i; simp
       right_inv := by intro x; funext i; simp
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } :
      (Fin (Fintype.card ι) → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toContinuousLinearEquiv
  have ha : AnalyticOnNhd ℝ (f ∘ L) (L.symm '' K) := by
    rintro _ ⟨x, hx, rfl⟩
    have hfx : AnalyticAt ℝ f (L (L.symm x)) := by simpa only [L.apply_symm_apply] using hf x hx
    exact hfx.comp (f := L) (L.analyticAt (L.symm x))
  obtain ⟨V, ho, hV, hd, hg⟩ := exists_ranDefinableOn_nhds_of_compact
    (hK.image L.symm.continuous) ha
  have hL : RanDefinableMap L.symm := by
    intro i
    exact ranDefinableFun_coordinate (e.symm i)
  refine ⟨L.symm ⁻¹' V, ho.preimage L.symm.continuous, ?_, hd.preimage_map hL, ?_⟩
  · intro x hx
    exact hV (mem_image_of_mem _ hx)
  · apply (hg.preimage_map hL).congr
    intro x _
    simp only [Function.comp_apply, L.apply_symm_apply]

theorem ranDefinableOn_of_analyticOnNhd_compact_closure_finite {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {S : Set (ι → ℝ)} (hS : RanDefinable S)
    (hc : IsCompact (closure S)) (hf : AnalyticOnNhd ℝ f (closure S)) :
    RanDefinableOn f S := by
  obtain ⟨U, _, hU, _, hfU⟩ := exists_ranDefinableOn_nhds_of_compact_finite hc hf
  exact hfU.restrict hS (subset_closure.trans hU)

theorem ranDefinable_bounded_analytic_sublevel_finite {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {S : Set (ι → ℝ)}
    (hc : IsCompact (closure S)) (hf : AnalyticOnNhd ℝ f (closure S))
    (hS : S = {x | f x < 0}) : RanDefinable S := by
  obtain ⟨U, _, hU, _, hfU⟩ := exists_ranDefinableOn_nhds_of_compact_finite hc hf
  have he : {x | x ∈ U ∧ f x < 0} = S := by
    ext x
    rw [hS]
    exact ⟨And.right, fun hx => ⟨hU (subset_closure (hS ▸ hx)), hx⟩⟩
  rw [← he]
  exact hfU.sublevel 0

end PlanarNikodym
