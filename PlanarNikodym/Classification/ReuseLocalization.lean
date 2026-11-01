import PlanarNikodym.Core.PositiveParts
import PlanarNikodym.Classification.CoveredTransfer

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

def Family.Foliations.zero : Family.Foliations := ⟨fun _ _ => 0, fun _ => contDiff_const⟩

theorem Family.LocallyReused.reused {d : ℕ} {G : Family 2 d} {p : Parameters 2 d}
    (h : G.LocallyReused p) : G.Reused (G.curve p) := by
  have hp := h.2 univ (by simp)
  simpa only [Family.Reused, Family.centersOf, inter_univ] using hp

theorem Family.locallyReused_restrict_mono {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) (hUW : U ⊆ G.W) (p : Parameters 2 d)
    (h : (G.restrictTo U).LocallyReused p) : G.LocallyReused p := by
  refine ⟨hUW h.1, ?_⟩
  intro V hV
  apply (h.2 V hV).mono
  rintro z ⟨q, ⟨⟨hq, he⟩, hqV⟩, rfl⟩
  exact ⟨q, ⟨⟨hUW hq, he⟩, hqV⟩, rfl⟩

theorem Family.locallyReused_restrict_of_nhds {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) (p : Parameters 2 d) (hU : U ∈ 𝓝 p)
    (h : G.LocallyReused p) : (G.restrictTo U).LocallyReused p := by
  refine ⟨mem_of_mem_nhds hU, ?_⟩
  intro V hV
  apply (h.2 (U ∩ V) (inter_mem hU hV)).mono
  rintro z ⟨q, ⟨⟨_, he⟩, hqU, hqV⟩, rfl⟩
  exact ⟨q, ⟨⟨hqU, he⟩, hqV⟩, rfl⟩

theorem Family.localReuseNotCovered_restrict_mono {d : ℕ} (G : Family 2 d)
    (U : Set (Parameters 2 d)) (hUW : U ⊆ G.W)
    (h : (G.restrictTo U).LocalReuseNotCovered) : G.LocalReuseNotCovered := by
  intro V
  apply (h V).mono
  rintro z ⟨u, hl, hn⟩
  exact ⟨u, G.locallyReused_restrict_mono U hUW (z, u) hl, hn⟩

theorem Family.not_localReuseNotCovered_of_strong {d : ℕ} (G : Family 2 d)
    (h : G.ReusedStronglyCovered) : ¬ G.LocalReuseNotCovered := by
  obtain ⟨V, hV⟩ := h
  intro hn
  obtain ⟨z, u, hl, hnc⟩ := (hn V).nonempty
  exact hnc (hV (z, u) hl.1 hl.reused)

theorem Family.not_localReuseNotCovered_of_null_cover {d : ℕ} (G : Family 2 d)
    (h : G.LocallyReusedCovered) : ¬ G.LocalReuseNotCovered := by
  obtain ⟨V, hV⟩ := h
  exact fun hn => HasPositivePart.not_of_null hV (hn V)

/-- Finite unions are explicitly enumerated by ℕ, including the empty case. -/
def Family.Foliations.finiteUnion {N : ℕ} (V : Fin N → Family.Foliations) : Family.Foliations :=
  Family.Foliations.iUnion (fun n => if h : n < N then V ⟨n, h⟩ else Family.Foliations.zero)

theorem Family.covered_finiteUnion {d N : ℕ} (G : Family 2 d)
    (V : Fin N → Family.Foliations) (i : Fin N) (p : Parameters 2 d)
    (h : G.Covered (V i) p) : G.Covered (Family.Foliations.finiteUnion V) p := by
  apply G.covered_iUnion _ i.val p
  simpa only [dif_pos i.isLt] using h

end PlanarNikodym
