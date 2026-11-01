import PlanarNikodym.Geometry.AnalyticIntervalPartition
import Mathlib.Order.Interval.Set.Infinite

/-! Finite point deletion in a real interval, including closed and singleton
intervals. Nonemptiness after deletion is essential at singleton intervals. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

theorem ordConnected_subset_closure_sdiff_finite {C F : Set ℝ}
    (hC : C.OrdConnected) (hF : F.Finite) (hne : (C \ F).Nonempty) :
    C ⊆ closure (C \ F) := by
  obtain ⟨a, ha, haF⟩ := hne
  intro x hx
  by_cases hxa : x = a
  · exact subset_closure ⟨hx, hxa ▸ haF⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases lt_or_gt_of_ne hxa with hxa | hax
  · have hb : x < min a (x + ε) := lt_min hxa (lt_add_of_pos_right x hε)
    obtain ⟨y, hy, hyF⟩ := ((Set.Ioo_infinite hb).sdiff hF).nonempty
    have hyC : y ∈ C := hC.out hx ha
      ⟨hy.1.le, (lt_min_iff.mp hy.2).1.le⟩
    refine ⟨y, ⟨hyC, hyF⟩, ?_⟩
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hy.1)]
    linarith [(lt_min_iff.mp hy.2).2]
  · have hb : max a (x - ε) < x := max_lt hax (sub_lt_self x hε)
    obtain ⟨y, hy, hyF⟩ := ((Set.Ioo_infinite hb).sdiff hF).nonempty
    have hyC : y ∈ C := hC.out ha hx
      ⟨(max_lt_iff.mp hy.1).1.le, hy.2.le⟩
    refine ⟨y, ⟨hyC, hyF⟩, ?_⟩
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hy.2)]
    linarith [(max_lt_iff.mp hy.1).2]

theorem ordConnected_subsingleton_of_finite {C : Set ℝ}
    (hC : C.OrdConnected) (hF : C.Finite) : C.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · exact (Set.Ioo_infinite hxy).not_finite
      (hF.subset (fun _ ht => hC.out hx hy ⟨ht.1.le, ht.2.le⟩))
  · exact (Set.Ioo_infinite hyx).not_finite
      (hF.subset (fun _ ht => hC.out hy hx ⟨ht.1.le, ht.2.le⟩))

end PlanarNikodym
