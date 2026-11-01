import PlanarNikodym.Core.Definitions

noncomputable section
namespace PlanarNikodym.Family
open Submodule Module
variable {d : ℕ} (G : PlanarNikodym.Family 2 d) (p : Parameters 2 d)

instance pointSpace_finite : FiniteDimensional ℝ (G.pointSpace p) := by
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range (G.uColumn p))
instance curveSpace_finite : FiniteDimensional ℝ (G.curveSpace p) := by
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range (G.zColumn p))
  unfold curveSpace
  infer_instance

theorem pointRank_le_aux : G.pointRank p ≤ d := by
  change Module.finrank ℝ (span ℝ (Set.range (G.uColumn p))) ≤ d
  have h := finrank_range_le_card (R := ℝ) (G.uColumn p)
  rw [Fintype.card_fin] at h
  exact h

theorem pointRank_le_curveRank : G.pointRank p ≤ G.curveRank p :=
  Submodule.finrank_mono le_sup_left

theorem curveRank_le_pointRank_add_two : G.curveRank p ≤ G.pointRank p + 2 := by
  letI := FiniteDimensional.span_of_finite ℝ (Set.finite_range (G.zColumn p))
  have hz : finrank ℝ (span ℝ (Set.range (G.zColumn p))) ≤ 2 := by
    exact finrank_range_le_card (R := ℝ) (G.zColumn p)
  exact (Submodule.finrank_add_le_finrank_add_finrank
    (G.pointSpace p) (span ℝ (Set.range (G.zColumn p)))).trans (Nat.add_le_add_left hz _)

theorem curveRank_le_parameters : G.curveRank p ≤ d + 2 :=
  (G.curveRank_le_pointRank_add_two p).trans (Nat.add_le_add_right (G.pointRank_le_aux p) 2)

theorem rank_trichotomy :
    G.curveRank p = G.pointRank p ∨ G.curveRank p = G.pointRank p + 1 ∨
      G.curveRank p = G.pointRank p + 2 := by
  have := G.pointRank_le_curveRank p
  have := G.curveRank_le_pointRank_add_two p
  omega

@[simp] theorem pointRank_zero_aux (G : PlanarNikodym.Family 2 0)
    (p : Parameters 2 0) : G.pointRank p = 0 := by
  exact Nat.eq_zero_of_le_zero (G.pointRank_le_aux p)

end PlanarNikodym.Family
