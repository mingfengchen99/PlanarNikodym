import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-! A continuous selector from finitely many continuous, pointwise distinct
real graphs chooses one fixed graph on each preconnected base subset. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [TopologicalSpace E]

def finiteGraphSelectorIndex {n : ℕ} (r : Fin n → E → ℝ) (θ : E → ℝ) (x : E) : Fin (n + 1) :=
  if h : ∃ i, θ x = r i x then (Classical.choose h).castSucc else Fin.last n

omit [TopologicalSpace E] in
theorem finiteGraphSelectorIndex_eq {n : ℕ} (r : Fin n → E → ℝ) (θ : E → ℝ)
    (x : E) (hi : Function.Injective (fun i => r i x)) (j : Fin n)
    (hj : θ x = r j x) : finiteGraphSelectorIndex r θ x = j.castSucc := by
  classical
  rw [finiteGraphSelectorIndex, dif_pos ⟨j, hj⟩]
  exact congrArg Fin.castSucc (hi ((Classical.choose_spec (show ∃ i, θ x = r i x from ⟨j, hj⟩)).symm.trans hj))

theorem continuousOn_finiteGraphSelectorIndex {n : ℕ} (C : Set E)
    (r : Fin n → E → ℝ) (θ : E → ℝ)
    (hr : ∀ i, ContinuousOn (r i) C) (hθ : ContinuousOn θ C)
    (hi : ∀ x ∈ C, Function.Injective (fun i => r i x))
    (hcover : ∀ x ∈ C, ∃ i, θ x = r i x) :
    ContinuousOn (finiteGraphSelectorIndex r θ) C := by
  intro x hx
  obtain ⟨j, hj⟩ := hcover x hx
  have hne (l : Fin n) : ∀ᶠ y in 𝓝[C] x, l ≠ j → θ y ≠ r l y := by
    by_cases hlj : l = j
    · exact Filter.Eventually.of_forall (fun y h => False.elim (h hlj))
    · have hn : θ x - r l x ≠ 0 := by
        intro he
        exact hlj (hi x hx ((sub_eq_zero.mp he).symm.trans hj))
      filter_upwards [((hθ x hx).sub (hr l x hx)).tendsto.eventually_ne hn] with y hy _
      exact sub_ne_zero.mp hy
  apply continuousWithinAt_const.congr_of_eventuallyEq ?_ (finiteGraphSelectorIndex_eq r θ x (hi x hx) j hj)
  filter_upwards [self_mem_nhdsWithin, Filter.eventually_all.mpr hne] with y hy hny
  obtain ⟨l, hl⟩ := hcover y hy
  have hlj : l = j := by
    by_contra hlj
    exact hny l hlj hl
  subst l
  exact finiteGraphSelectorIndex_eq r θ y (hi y hy) j hl

/-- Finite separated graphs cannot exchange a continuous selector on a
preconnected subset, including a nonopen or singular parameter subset. -/
theorem continuous_selector_eq_on_preconnected {n : ℕ} (C : Set E)
    (hC : IsPreconnected C) (r : Fin n → E → ℝ) (θ : E → ℝ)
    (hr : ∀ i, ContinuousOn (r i) C) (hθ : ContinuousOn θ C)
    (hi : ∀ x ∈ C, Function.Injective (fun i => r i x))
    (hcover : ∀ x ∈ C, ∃ i, θ x = r i x)
    {x₀ : E} (hx₀ : x₀ ∈ C) (j : Fin n) (hj : θ x₀ = r j x₀) :
    ∀ x ∈ C, θ x = r j x := by
  intro x hx
  obtain ⟨l, hl⟩ := hcover x hx
  have he := hC.constant (continuousOn_finiteGraphSelectorIndex C r θ hr hθ hi hcover) hx hx₀
  rw [finiteGraphSelectorIndex_eq r θ x (hi x hx) l hl,
    finiteGraphSelectorIndex_eq r θ x₀ (hi x₀ hx₀) j hj] at he
  exact (Fin.castSucc_injective n he) ▸ hl

end PlanarNikodym
