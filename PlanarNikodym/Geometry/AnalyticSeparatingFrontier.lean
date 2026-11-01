import PlanarNikodym.Geometry.LocalAnalyticConnectedRefinement
import PlanarNikodym.Geometry.AnalyticSignRefinementCoordinates
import PlanarNikodym.Geometry.PolynomialThomSigns

/-! Relative weak-sign frontiers and the two elementary transport steps
used in analytic dimension induction: adding the original functions and
changing coordinates. -/
noncomputable section
open Set
namespace PlanarNikodym

def analyticWeakSignCell {X I : Type*} (U : Set X)
    (f : I → X → ℝ) (s : I → Fin 3) : Set X :=
  {x | x ∈ U ∧ ∀ i, polynomialSignCondition true (s i) (f i x)}

def LocalAnalyticSeparatingFrontier (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ {J : Type} [Fintype J] (f : J → E → ℝ) (x₀ : E),
    (∀ j, AnalyticAt ℝ (f j) x₀) → ∀ O : Set E, IsOpen O → x₀ ∈ O →
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
        (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
        (∀ j, ∃ k, EqOn (g k) (f j) U) ∧
        ∀ s, analyticStrongSignCell U g s = ∅ ∨
          (IsConnected (analyticStrongSignCell U g s) ∧
            closure (analyticStrongSignCell U g s) ∩ U = analyticWeakSignCell U g s)

theorem closure_analyticStrongSignCell_inter_subset_weak
    {X I : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (f : I → X → ℝ) (hf : ∀ i, ContinuousOn (f i) U) (s : I → Fin 3) :
    closure (analyticStrongSignCell U f s) ∩ U ⊆ analyticWeakSignCell U f s := by
  rintro x ⟨hx, hxU⟩
  refine ⟨hxU, fun i => ?_⟩
  have hw : f i x ∈ closure {r | polynomialSignCondition true (s i) r} :=
    ((hf i x hxU).continuousAt (hU.mem_nhds hxU)).continuousWithinAt.mem_closure hx
      (fun _ hy => polynomialSignCondition_weaken (hy.2 i))
  rwa [(isClosed_polynomialWeakSignCondition (s i)).closure_eq] at hw

theorem analyticStrongSignCell_sum_frontier_or_empty
    {X I J : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (f : I → X → ℝ) (g : J → X → ℝ)
    (hf : ∀ i, ContinuousOn (f i) U) (hgc : ∀ j, ContinuousOn (g j) U)
    (hz : ∀ i, (∀ x ∈ U, f i x = 0) ∨
      ∃ j, ∀ x ∈ U, f i x = 0 ↔ g j x = 0)
    (hg : ∀ t, analyticStrongSignCell U g t = ∅ ∨
      (IsConnected (analyticStrongSignCell U g t) ∧
        closure (analyticStrongSignCell U g t) ∩ U = analyticWeakSignCell U g t))
    (s : I ⊕ J → Fin 3) :
    analyticStrongSignCell U (Sum.elim f g) s = ∅ ∨
      (IsConnected (analyticStrongSignCell U (Sum.elim f g) s) ∧
        closure (analyticStrongSignCell U (Sum.elim f g) s) ∩ U =
          analyticWeakSignCell U (Sum.elim f g) s) := by
  have hgconn t := (hg t).imp id (fun h => h.1)
  rcases analyticStrongSignCell_sum_eq_right_or_empty U f g hf hz hgconn s with he | he
  · exact Or.inl he
  · rcases hg (fun j => s (Sum.inr j)) with hgE | ⟨hgC, hgF⟩
    · exact Or.inl (he.trans hgE)
    · right
      refine ⟨he.symm ▸ hgC, Set.Subset.antisymm ?_ ?_⟩
      · apply closure_analyticStrongSignCell_inter_subset_weak U hU
        rintro (i | j)
        · exact hf i
        · exact hgc j
      · intro x hx
        have hxg : x ∈ analyticWeakSignCell U g (fun j => s (Sum.inr j)) :=
          ⟨hx.1, fun j => hx.2 (Sum.inr j)⟩
        rw [← hgF, ← he] at hxg
        exact hxg

theorem analyticStrongSignCell_frontier_homeomorph
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (U : Set Y) (f : I → Y → ℝ)
    (h : ∀ s, analyticStrongSignCell U f s = ∅ ∨
      (IsConnected (analyticStrongSignCell U f s) ∧
        closure (analyticStrongSignCell U f s) ∩ U = analyticWeakSignCell U f s))
    (s : I → Fin 3) :
    analyticStrongSignCell (e ⁻¹' U) (fun i x => f i (e x)) s = ∅ ∨
      (IsConnected (analyticStrongSignCell (e ⁻¹' U) (fun i x => f i (e x)) s) ∧
        closure (analyticStrongSignCell (e ⁻¹' U) (fun i x => f i (e x)) s) ∩ (e ⁻¹' U) =
          analyticWeakSignCell (e ⁻¹' U) (fun i x => f i (e x)) s) := by
  rw [analyticStrongSignCell_preimage]
  rcases h s with he | ⟨hc, hcl⟩
  · exact Or.inl (by rw [he]; exact preimage_empty)
  · right
    refine ⟨e.isConnected_preimage.mpr hc, ?_⟩
    rw [← e.preimage_closure, ← preimage_inter, hcl]
    rfl

end PlanarNikodym
