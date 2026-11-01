import PlanarNikodym.Geometry.AnalyticPreparationSimpleRoot
import PlanarNikodym.Geometry.CompactFiberExclusion
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Normed.Module.Connected

/-! Complete finite analytic branches for a compact interval of simple real roots. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An actual simple root has an analytic branch and an exact local zero-set description. -/
theorem exists_analytic_simple_root_branch
    (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) (hz : f (x₀, t₀) = 0)
    (hd : deriv (fun t => f (x₀, t)) t₀ ≠ 0) :
    ∃ (U : Set E) (V : Set ℝ) (ρ : E → ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t₀ ∈ V ∧ ρ x₀ = t₀ ∧
      MapsTo ρ U V ∧ AnalyticOnNhd ℝ ρ U ∧
      ∀ x ∈ U, ∀ t ∈ V, f (x, t) = 0 ↔ t = ρ x := by
  obtain ⟨U, V, ρ, u, hU, hxU, hV, htV, hρ₀, hρV, hρ, hu, heq⟩ :=
    exists_analytic_simple_root_preparation_on f x₀ t₀ hf hz hd
  refine ⟨U, V, ρ, hU, hxU, hV, htV, hρ₀, hρV, hρ, ?_⟩
  intro x hx t ht
  obtain ⟨hun, hfactor⟩ := heq (x, t) ⟨hx, ht⟩
  rw [hfactor, mul_eq_zero, or_iff_left hun, sub_eq_zero]

/-- The zero set on a compact interval is finite if every root is simple.
Only joint analyticity along the distinguished fiber is assumed. -/
theorem finite_simple_analytic_fiber_zeros
    (f : E × ℝ → ℝ) (x₀ : E) (A B : ℝ)
    (hf : ∀ t ∈ Icc A B, AnalyticAt ℝ f (x₀, t))
    (hd : ∀ t ∈ Icc A B, f (x₀, t) = 0 →
      deriv (fun s => f (x₀, s)) t ≠ 0) :
    {t : ℝ | t ∈ Icc A B ∧ f (x₀, t) = 0}.Finite := by
  let Z : Set ℝ := {t | t ∈ Icc A B ∧ f (x₀, t) = 0}
  have hc : ContinuousOn (fun t => f (x₀, t)) (Icc A B) := by
    intro t ht
    exact ((hf t ht).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hclosed : IsClosed Z :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact Z :=
    isCompact_Icc.of_isClosed_subset hclosed (fun _ h => h.1)
  apply hcompact.finite
  apply isDiscrete_iff_forall_exists_isOpen.mpr
  intro t ht
  obtain ⟨U, V, ρ, hU, hxU, hV, htV, hρ₀, hρV, hρ, hroots⟩ :=
    exists_analytic_simple_root_branch f x₀ t (hf t ht.1) ht.2 (hd t ht.1 ht.2)
  refine ⟨V, hV, ?_⟩
  ext s
  constructor
  · intro hs
    exact mem_singleton_iff.mpr ((hroots x₀ hxU s hs.1).mp hs.2.2 |>.trans hρ₀)
  · intro hs
    rcases mem_singleton_iff.mp hs with rfl
    exact ⟨htV, ht⟩

end PlanarNikodym
