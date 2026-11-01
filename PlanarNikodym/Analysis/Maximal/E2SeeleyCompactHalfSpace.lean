import PlanarNikodym.Analysis.Maximal.E2SeeleyHalfSpace
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Compact support supplies the derivative bounds required by the
constructed Seeley series. No extension or derivative-bound input remains. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem e2_compact_contDiffOn_jets_bounded {s : Set E} (hs : IsClosed s)
    (hu : UniqueDiffOn ℝ s) {f : E → F} (hf : ContDiffOn ℝ ∞ f s)
    (hc : HasCompactSupport f) :
    ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, ‖ftaylorSeriesWithin ℝ f s x m‖ ≤ M := by
  intro m
  have hm : (m : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)
  have hp := hf.ftaylorSeriesWithin hu
  obtain ⟨C, hC⟩ := (hc.isCompact.inter_right hs).exists_bound_of_continuousOn
    ((hp.cont m hm).mono inter_subset_right)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  by_cases hxs : x ∈ tsupport f
  · exact (hC x ⟨hxs, hx⟩).trans (le_max_left _ _)
  · have he : f =ᶠ[𝓝[s] x] 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hxs).filter_mono inf_le_left
    have hz : f x = 0 := (notMem_tsupport_iff_eventuallyEq.mp hxs).self_of_nhds
    have hj := he.iteratedFDerivWithin_eq (𝕜 := ℝ) hz m
    change ‖iteratedFDerivWithin ℝ m f s x‖ ≤ max C 0
    rw [hj, iteratedFDerivWithin_zero, Pi.zero_apply, norm_zero]
    exact le_max_right _ _

variable [CompleteSpace F]

theorem e2PositiveHalfSpace_uniqueDiffOn : UniqueDiffOn ℝ (e2PositiveHalfSpace E) := by
  apply uniqueDiffOn_convex (e2PositiveHalfSpace_convex E)
  refine ⟨(1, 0), ?_⟩
  simp [e2PositiveHalfSpace, interior_prod_eq]

theorem e2SeeleyExtension_contDiff_of_compact_contDiffOn
    {f : (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (e2PositiveHalfSpace E))
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (e2SeeleyExtension f) := by
  have hb := e2_compact_contDiffOn_jets_bounded (e2PositiveHalfSpace_isClosed E)
    e2PositiveHalfSpace_uniqueDiffOn hf hc
  choose M hM hb using hb
  exact e2SeeleyExtension_contDiff (hf.ftaylorSeriesWithin e2PositiveHalfSpace_uniqueDiffOn)
    M hM hb

end PlanarNikodym
