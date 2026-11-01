import PlanarNikodym.Geometry.AnalyticStratificationChartTopology
import PlanarNikodym.Geometry.AnalyticSeparatingFrontier

/-! The dimension-induction conclusion with actual analytic stratum charts.
The elementary refinement and coordinate changes preserve both the
constructed charts and the already proved exact weak-sign frontier formula. -/
noncomputable section
open Set
namespace PlanarNikodym

def LocalAnalyticStratumRefinement (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ {J : Type} [Fintype J] (f : J → E → ℝ) (x₀ : E),
    (∀ j, AnalyticAt ℝ (f j) x₀) → ∀ O : Set E, IsOpen O → x₀ ∈ O →
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
        (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
        (∀ j, ∃ k, EqOn (g k) (f j) U) ∧
        ∀ s, analyticStrongSignCell U g s = ∅ ∨
          ∃ Q : AnalyticStratificationChart E,
            Q.image = analyticStrongSignCell U g s ∧
            closure (analyticStrongSignCell U g s) ∩ U = analyticWeakSignCell U g s

theorem analyticStrongSignCell_sum_stratum_or_empty
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {I J : Type}
    (U : Set E) (hU : IsOpen U) (f : I → E → ℝ) (g : J → E → ℝ)
    (hf : ∀ i, ContinuousOn (f i) U) (hgc : ∀ j, ContinuousOn (g j) U)
    (hz : ∀ i, (∀ x ∈ U, f i x = 0) ∨
      ∃ j, ∀ x ∈ U, f i x = 0 ↔ g j x = 0)
    (hg : ∀ t, analyticStrongSignCell U g t = ∅ ∨
      ∃ Q : AnalyticStratificationChart E, Q.image = analyticStrongSignCell U g t ∧
        closure (analyticStrongSignCell U g t) ∩ U = analyticWeakSignCell U g t)
    (s : I ⊕ J → Fin 3) :
    analyticStrongSignCell U (Sum.elim f g) s = ∅ ∨
      ∃ Q : AnalyticStratificationChart E, Q.image = analyticStrongSignCell U (Sum.elim f g) s ∧
        closure (analyticStrongSignCell U (Sum.elim f g) s) ∩ U =
          analyticWeakSignCell U (Sum.elim f g) s := by
  have hgfront t : analyticStrongSignCell U g t = ∅ ∨
      (IsConnected (analyticStrongSignCell U g t) ∧
        closure (analyticStrongSignCell U g t) ∩ U = analyticWeakSignCell U g t) := by
    rcases hg t with he | ⟨Q, hQ, hcl⟩
    · exact Or.inl he
    · exact Or.inr ⟨hQ ▸ Q.connected_image, hcl⟩
  rcases analyticStrongSignCell_sum_frontier_or_empty U hU f g hf hgc hz hgfront s with he | ⟨_, hcl⟩
  · exact Or.inl he
  · have hgconn t := (hgfront t).imp id (fun h => h.1)
    rcases analyticStrongSignCell_sum_eq_right_or_empty U f g hf hz hgconn s with he | he
    · exact Or.inl he
    · rcases hg (fun j => s (Sum.inr j)) with hgE | ⟨Q, hQ, _⟩
      · exact Or.inl (he.trans hgE)
      · exact Or.inr ⟨Q, hQ.trans he.symm, hcl⟩

theorem analyticStrongSignCell_stratum_homeomorph
    {E F I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₜ F) (he : ∀ x, AnalyticAt ℝ e x) (hei : ∀ y, AnalyticAt ℝ e.symm y)
    (U : Set E) (f : I → E → ℝ)
    (h : ∀ s, analyticStrongSignCell U f s = ∅ ∨
      ∃ Q : AnalyticStratificationChart E, Q.image = analyticStrongSignCell U f s ∧
        closure (analyticStrongSignCell U f s) ∩ U = analyticWeakSignCell U f s)
    (s : I → Fin 3) :
    analyticStrongSignCell (e.symm ⁻¹' U) (fun i y => f i (e.symm y)) s = ∅ ∨
      ∃ Q : AnalyticStratificationChart F,
        Q.image = analyticStrongSignCell (e.symm ⁻¹' U) (fun i y => f i (e.symm y)) s ∧
        closure (analyticStrongSignCell (e.symm ⁻¹' U) (fun i y => f i (e.symm y)) s) ∩
          (e.symm ⁻¹' U) = analyticWeakSignCell (e.symm ⁻¹' U) (fun i y => f i (e.symm y)) s := by
  have hfront t : analyticStrongSignCell U f t = ∅ ∨
      (IsConnected (analyticStrongSignCell U f t) ∧
        closure (analyticStrongSignCell U f t) ∩ U = analyticWeakSignCell U f t) := by
    rcases h t with he | ⟨Q, hQ, hcl⟩
    · exact Or.inl he
    · exact Or.inr ⟨hQ ▸ Q.connected_image, hcl⟩
  rcases h s with hE | ⟨Q, hQ, _⟩
  · left
    rw [analyticStrongSignCell_preimage, hE]
    exact preimage_empty
  · let P := Q.postcompose e e.symm (fun x _ => he x) (fun y _ => hei y)
      (fun x _ => e.symm_apply_apply x)
    have himage : P.image = analyticStrongSignCell (e.symm ⁻¹' U) (fun i y => f i (e.symm y)) s := by
      rw [AnalyticStratificationChart.postcompose_image, hQ,
        e.image_eq_preimage_symm, analyticStrongSignCell_preimage]
    have htarget := analyticStrongSignCell_frontier_homeomorph e.symm U f hfront s
    rcases htarget with hE | ⟨_, hcl⟩
    · exact Or.inl hE
    · exact Or.inr ⟨P, himage, hcl⟩

end PlanarNikodym
