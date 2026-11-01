import PlanarNikodym.Core.Definitions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! Compactness of the time interval gives one actual open parameter
neighborhood of the whole parameter closure on which the unchanged
ambient defining function remains jointly analytic. -/
noncomputable section
open Set
namespace PlanarNikodym

def Family.analyticParameterNeighborhood {n d : ℕ} (G : Family n d) :
    Set (Parameters n d) :=
  {p | ∀ t ∈ G.I.carrier,
    AnalyticAt ℝ (fun x : ℝ × Parameters n d => G.γ x.1 x.2) (t, p)}

theorem Family.isOpen_analyticParameterNeighborhood {n d : ℕ} (G : Family n d) :
    IsOpen G.analyticParameterNeighborhood := by
  apply isOpen_iff_forall_mem_open.mpr
  intro p hp
  obtain ⟨U, V, _, hV, hIU, hpV, hUV⟩ := generalized_tube_lemma
    (show IsCompact G.I.carrier from isCompact_Icc) isCompact_singleton
    (isOpen_analyticAt ℝ (fun x : ℝ × Parameters n d => G.γ x.1 x.2))
    (by rintro ⟨t, q⟩ ⟨ht, hq⟩; have he : q = p := hq; subst q; exact hp t ht)
  refine ⟨V, ?_, hV, hpV (mem_singleton p)⟩
  intro q hq t ht
  exact hUV ⟨hIU ht, hq⟩

theorem Family.closure_subset_analyticParameterNeighborhood {n d : ℕ}
    (G : Family n d) (ha : G.IsAnalyticAtClosure) :
    closure G.W ⊆ G.analyticParameterNeighborhood := by
  intro p hp t ht
  exact ha (t, p) ⟨ht, hp⟩

theorem Family.isAnalytic_on_analyticParameterNeighborhood {n d : ℕ}
    (G : Family n d) :
    AnalyticOnNhd ℝ (fun x : ℝ × Parameters n d => G.γ x.1 x.2)
      (G.I.carrier ×ˢ G.analyticParameterNeighborhood) := by
  rintro ⟨t, p⟩ ⟨ht, hp⟩
  exact hp t ht

end PlanarNikodym
