import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A boundary-vanishing positive function attains its fiber maximum
inside the original bounded set. The set need not be closed, connected,
or a manifold. No choice of a point in each fiber is used as a substitute
for semianalyticity of the eventual critical locus. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem exists_positive_fiber_maximum
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace F] [T2Space F]
    {S : Set E} (hb : Bornology.IsBounded S) (L : E → F) (hL : Continuous L)
    (g : E → ℝ) (hg : ContinuousOn g (closure S))
    (hpos : ∀ x ∈ S, 0 < g x) (hzero : ∀ x ∈ closure S \ S, g x = 0)
    {x : E} (hx : x ∈ S) :
    ∃ y ∈ S, L y = L x ∧ 0 < g y ∧
      ∀ z ∈ closure S, L z = L x → g z ≤ g y := by
  let K := closure S ∩ L ⁻¹' {L x}
  have hK : IsCompact K := hb.isCompact_closure.inter_right
    (isClosed_singleton.preimage hL)
  have hxK : x ∈ K := ⟨subset_closure hx, rfl⟩
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ (hg.mono inter_subset_left)
  have hyp : 0 < g y := (hpos x hx).trans_le (hmax hxK)
  have hyS : y ∈ S := by
    by_contra hn
    exact (ne_of_gt hyp) (hzero y ⟨hy.1, hn⟩)
  exact ⟨y, hyS, hy.2, hyp, fun z hz he => hmax ⟨hz, he⟩⟩

end PlanarNikodym
