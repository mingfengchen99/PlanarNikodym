import PlanarNikodym.Classification.CountableLocalization
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym

theorem Family.IsAnalyticAtClosure.isAnalytic {d : ℕ} {G : Family 2 d}
    (ha : G.IsAnalyticAtClosure) : G.IsAnalytic :=
  fun x hx => ha x ⟨hx.1, subset_closure hx.2⟩

structure BallParameterCover {d : ℕ} (G : Family 2 d) where
  center : ℕ → Parameters 2 d
  radius : ℕ → ℝ
  radius_pos : ∀ i, 0 < radius i
  closure_subset : ∀ i, closure (ball (center i) (radius i)) ⊆ G.W
  covers : G.W ⊆ ⋃ i, ball (center i) (radius i)

def BallParameterCover.toOpenParameterCover {d : ℕ} {G : Family 2 d}
    (C : BallParameterCover G) : OpenParameterCover G where
  domain := fun i => ball (C.center i) (C.radius i)
  isOpen := fun _ => isOpen_ball
  subset := fun i => subset_closure.trans (C.closure_subset i)
  covers := C.covers

/-- Every nonempty open parameter domain has a countable bounded-ball cover
whose closures stay inside the original domain. -/
theorem exists_ball_parameter_cover {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (hne : G.W.Nonempty) : Nonempty (BallParameterCover G) := by
  classical
  haveI : Nonempty G.W := hne.to_subtype
  have hball (p : G.W) : ∃ r : ℝ, 0 < r ∧ closure (ball p.val r) ⊆ G.W := by
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds p.property)
    exact ⟨r / 2, half_pos hr,
      closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hr)).trans hsub)⟩
  choose r hr hsub using hball
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof G.W).indexed_countable_subcover
    (fun p : G.W => ball p.val (r p)) (fun _ => isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (hr ⟨p, hp⟩)⟩)
  exact ⟨⟨fun i => (f i).val, fun i => r (f i), fun i => hr (f i), fun i => hsub (f i), hf⟩⟩

end PlanarNikodym
