import PlanarNikodym.Geometry.AnalyticStratificationRefinement
import PlanarNikodym.Geometry.AnalyticStratificationThomFaces

/-! Coherent numerical dimensions for the actual analytic sign charts.
The dimension labels and their strict face relation form the strengthened
induction conclusion, not an assumed stratification theorem. -/
noncomputable section
open Set
namespace PlanarNikodym

def AnalyticDimensionedSignCells {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (g : I → E → ℝ) (δ : (I → Fin 3) → ℕ) : Prop :=
  (∀ s, analyticStrongSignCell U g s = ∅ ∨
    ∃ Q : AnalyticStratificationChart E,
      Q.image = analyticStrongSignCell U g s ∧ Q.dim = δ s ∧
      closure (analyticStrongSignCell U g s) ∩ U = analyticWeakSignCell U g s) ∧
  ∀ s t, s ≠ t → (analyticStrongSignCell U g s).Nonempty →
    (analyticStrongSignCell U g t).Nonempty → polynomialThomFace t s → δ t < δ s

def LocalAnalyticDimensionedRefinement (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ {J : Type} [Fintype J] (f : J → E → ℝ) (x₀ : E),
    (∀ j, AnalyticAt ℝ (f j) x₀) → ∀ O : Set E, IsOpen O → x₀ ∈ O →
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ) (δ : (κ → Fin 3) → ℕ),
        (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
        (∀ j, ∃ k, EqOn (g k) (f j) U) ∧ AnalyticDimensionedSignCells U g δ

theorem AnalyticDimensionedSignCells.sum_refinement
    {E I J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) (f : I → E → ℝ) (g : J → E → ℝ)
    (δ : (J → Fin 3) → ℕ) (hf : ∀ i, ContinuousOn (f i) U)
    (hgc : ∀ j, ContinuousOn (g j) U)
    (hz : ∀ i, (∀ x ∈ U, f i x = 0) ∨ ∃ j, ∀ x ∈ U, f i x = 0 ↔ g j x = 0)
    (H : AnalyticDimensionedSignCells U g δ) :
    AnalyticDimensionedSignCells U (Sum.elim f g) (fun s => δ (fun j => s (Sum.inr j))) := by
  have hfront t : analyticStrongSignCell U g t = ∅ ∨
      (IsConnected (analyticStrongSignCell U g t) ∧
        closure (analyticStrongSignCell U g t) ∩ U = analyticWeakSignCell U g t) := by
    rcases H.1 t with he | ⟨Q, hQ, _, hcl⟩
    · exact Or.inl he
    · exact Or.inr ⟨hQ ▸ Q.connected_image, hcl⟩
  have hgconn t := (hfront t).imp id (fun h => h.1)
  have heq (s : I ⊕ J → Fin 3) (hs : (analyticStrongSignCell U (Sum.elim f g) s).Nonempty) :
      analyticStrongSignCell U (Sum.elim f g) s =
        analyticStrongSignCell U g (fun j => s (Sum.inr j)) :=
    (analyticStrongSignCell_sum_eq_right_or_empty U f g hf hz hgconn s).resolve_left hs.ne_empty
  refine ⟨?_, ?_⟩
  · intro s
    rcases (analyticStrongSignCell U (Sum.elim f g) s).eq_empty_or_nonempty with he | hs
    · exact Or.inl he
    · have he := heq s hs
      rcases H.1 (fun j => s (Sum.inr j)) with hE | ⟨Q, hQ, hdim, _⟩
      · exact Or.inl (he.trans hE)
      · rcases analyticStrongSignCell_sum_frontier_or_empty U hU f g hf hgc hz hfront s with hE | ⟨_, hcl⟩
        · exact Or.inl hE
        · exact Or.inr ⟨Q, hQ.trans he.symm, hdim, hcl⟩
  · intro s t hst hs ht hface
    have hsOld : (analyticStrongSignCell U g (fun j => s (Sum.inr j))).Nonempty := (heq s hs) ▸ hs
    have htOld : (analyticStrongSignCell U g (fun j => t (Sum.inr j))).Nonempty := (heq t ht) ▸ ht
    by_cases hproj : (fun j => s (Sum.inr j)) = fun j => t (Sum.inr j)
    · have heS := heq s hs
      obtain ⟨x, hxS⟩ := hs
      have hxOld := (Set.ext_iff.mp heS x).mp hxS
      rw [hproj] at hxOld
      have hxT := (Set.ext_iff.mp (heq t ht) x).mpr hxOld
      exact False.elim (hst (funext (fun q => (hxS.2 q).symm.trans (hxT.2 q))))
    · exact H.2 _ _ hproj hsOld htOld (fun j => hface (Sum.inr j))

theorem AnalyticDimensionedSignCells.homeomorph
    {E F I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₜ F) (he : ∀ x, AnalyticAt ℝ e x) (hei : ∀ y, AnalyticAt ℝ e.symm y)
    {U : Set E} {g : I → E → ℝ} {δ : (I → Fin 3) → ℕ}
    (H : AnalyticDimensionedSignCells U g δ) :
    AnalyticDimensionedSignCells (e.symm ⁻¹' U) (fun i y => g i (e.symm y)) δ := by
  have hfront t : analyticStrongSignCell U g t = ∅ ∨
      (IsConnected (analyticStrongSignCell U g t) ∧
        closure (analyticStrongSignCell U g t) ∩ U = analyticWeakSignCell U g t) := by
    rcases H.1 t with he | ⟨Q, hQ, _, hcl⟩
    · exact Or.inl he
    · exact Or.inr ⟨hQ ▸ Q.connected_image, hcl⟩
  refine ⟨?_, ?_⟩
  · intro s
    rcases H.1 s with hE | ⟨Q, hQ, hdim, _⟩
    · left
      rw [analyticStrongSignCell_preimage, hE]
      exact preimage_empty
    · let P := Q.postcompose e e.symm (fun x _ => he x) (fun y _ => hei y)
        (fun x _ => e.symm_apply_apply x)
      have himage : P.image = analyticStrongSignCell (e.symm ⁻¹' U) (fun i y => g i (e.symm y)) s := by
        rw [AnalyticStratificationChart.postcompose_image, hQ,
          e.image_eq_preimage_symm, analyticStrongSignCell_preimage]
      rcases analyticStrongSignCell_frontier_homeomorph e.symm U g hfront s with hE | ⟨_, hcl⟩
      · exact Or.inl hE
      · exact Or.inr ⟨P, himage, hdim, hcl⟩
  · intro s t hst hs ht hface
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    exact H.2 s t hst ⟨e.symm x, hx⟩ ⟨e.symm y, hy⟩ hface

end PlanarNikodym
