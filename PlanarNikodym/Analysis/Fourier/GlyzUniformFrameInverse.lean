import PlanarNikodym.Analysis.Fourier.GlyzContinuousProjection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

/-! A uniform inverse bound on all bounded finite-dimensional frames
whose actual determinants stay away from zero. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem glyz_ring_inverse_equiv (L : E ≃L[ℝ] E) :
    Ring.inverse L.toContinuousLinearMap = L.symm.toContinuousLinearMap := by
  have hL : IsUnit L.toContinuousLinearMap :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr L.bijective
  apply DFunLike.ext
  intro x
  apply L.injective
  have h := congrArg (fun A : E →L[ℝ] E => A x)
    (Ring.mul_inverse_cancel L.toContinuousLinearMap hL)
  simpa only [mul_apply_eq_comp, one_apply_eq_self,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h

theorem exists_uniform_glyz_frame_inverse {b : ℝ} (hb : 0 < b) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : E ≃L[ℝ] E,
      ‖L.toContinuousLinearMap‖ ≤ B → b ≤ |L.toLinearMap.det| →
        ‖L.symm.toContinuousLinearMap‖ ≤ C := by
  let K : Set (E →L[ℝ] E) := closedBall 0 B ∩ {A | b ≤ |A.det|}
  have hK : IsCompact K := (isCompact_closedBall (0 : E →L[ℝ] E) B).inter_right
    (isClosed_le continuous_const ContinuousLinearMap.continuous_det.abs)
  have hc : ContinuousOn (Ring.inverse : (E →L[ℝ] E) → E →L[ℝ] E) K := by
    intro A hA
    have hdet : A.det ≠ 0 := by
      intro hz
      have h := hA.2
      change b ≤ |A.det| at h
      rw [hz, abs_zero] at h
      exact (not_le_of_gt hb) h
    have hunit : IsUnit A := ContinuousLinearMap.isUnit_iff_bijective.mpr
      (A.toContinuousLinearEquivOfDetNeZero hdet).bijective
    obtain ⟨u, hu⟩ := hunit
    exact (hu ▸ NormedRing.inverse_continuousAt u).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro L hL hd
  have h := hC L.toContinuousLinearMap ⟨by simpa using hL, hd⟩
  rw [glyz_ring_inverse_equiv] at h
  exact h.trans ((le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one))

end PlanarNikodym
