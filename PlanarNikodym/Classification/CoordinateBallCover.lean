import PlanarNikodym.Classification.BallCover
import PlanarNikodym.Cells.FamilyIntrinsicRankCover

/-! Countable interior balls in the fixed finite parameter coordinates.
Their images give an actual open parameter cover of the original family. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

structure CoordinateBallParameterCover {d : ℕ} (G : Family 2 d) where
  center : ℕ → (Fin (d + 2) → ℝ)
  radius : ℕ → ℝ
  radius_pos : ∀ i, 0 < radius i
  closure_subset : ∀ i, closure (ball (center i) (radius i)) ⊆ (parameterFrame d) ⁻¹' G.W
  covers : (parameterFrame d) ⁻¹' G.W ⊆ ⋃ i, ball (center i) (radius i)

def CoordinateBallParameterCover.toOpenParameterCover {d : ℕ} {G : Family 2 d}
    (C : CoordinateBallParameterCover G) : OpenParameterCover G where
  domain i := (parameterFrame d) '' ball (C.center i) (C.radius i)
  isOpen i := (parameterFrame d).toHomeomorph.isOpenMap _ isOpen_ball
  subset i := by
    rintro _ ⟨x, hx, rfl⟩
    exact C.closure_subset i (subset_closure hx)
  covers := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (C.covers (by simpa using hp :
      (parameterFrame d).symm p ∈ (parameterFrame d) ⁻¹' G.W))
    exact mem_iUnion.mpr ⟨i, (parameterFrame d).symm p, hi,
      (parameterFrame d).apply_symm_apply p⟩

theorem exists_coordinate_ball_parameter_cover {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (hne : G.W.Nonempty) : Nonempty (CoordinateBallParameterCover G) := by
  classical
  let U := (parameterFrame d) ⁻¹' G.W
  have hU : IsOpen U := ho.preimage (parameterFrame d).continuous
  have hneU : U.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨(parameterFrame d).symm p, by simpa only [U, mem_preimage,
      ContinuousLinearEquiv.apply_symm_apply] using hp⟩
  letI : Nonempty U := hneU.to_subtype
  have hex (x : U) : ∃ r : ℝ, 0 < r ∧ closure (ball x.val r) ⊆ U := by
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds x.property)
    exact ⟨r / 2, half_pos hr, closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self hr)).trans hsub)⟩
  choose r hr hsub using hex
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof U).indexed_countable_subcover
    (fun x : U => ball x.val (r x)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  exact ⟨⟨fun i => (f i).val, fun i => r (f i), fun i => hr (f i), fun i => hsub (f i), hf⟩⟩

end PlanarNikodym
