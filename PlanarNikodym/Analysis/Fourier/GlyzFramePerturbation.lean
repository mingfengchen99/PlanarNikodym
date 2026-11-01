import PlanarNikodym.Analysis.Fourier.GlyzUniformFrameInverse
import Mathlib.Topology.MetricSpace.Thickening

/-! Uniform stability of actual invertible frames, including a bound
for the inverses of all nearby frames. -/
noncomputable section
open Set Metric
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_uniform_glyz_frame_perturbation {b : ℝ} (hb : 0 < b) (B : ℝ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ L : E ≃L[ℝ] E,
      ‖L.toContinuousLinearMap‖ ≤ B → b ≤ |L.toLinearMap.det| →
      ∀ A : E →L[ℝ] E, dist A L.toContinuousLinearMap < ε →
        ∃ T : E ≃L[ℝ] E, T.toContinuousLinearMap = A ∧
          ‖T.symm.toContinuousLinearMap‖ ≤ C := by
  let K : Set (E →L[ℝ] E) := closedBall 0 B ∩ {A | b ≤ |A.det|}
  have hK : IsCompact K := (isCompact_closedBall (0 : E →L[ℝ] E) B).inter_right
    (isClosed_le continuous_const ContinuousLinearMap.continuous_det.abs)
  have ho : IsOpen {A : E →L[ℝ] E | b / 2 < |A.det|} :=
    isOpen_lt continuous_const ContinuousLinearMap.continuous_det.abs
  obtain ⟨ε, hε, hthick⟩ := hK.exists_thickening_subset_open ho
    (fun A hA => (half_lt_self hb).trans_le hA.2)
  obtain ⟨C, hC, hinv⟩ := exists_uniform_glyz_frame_inverse (E := E) (half_pos hb) (B + 1)
  refine ⟨min ε 1, C, lt_min hε zero_lt_one, hC, ?_⟩
  intro L hL hd A hA
  have hm : L.toContinuousLinearMap ∈ K := ⟨by simpa using hL, hd⟩
  have hdet : b / 2 < |A.det| := hthick
    (mem_thickening_iff.mpr ⟨L.toContinuousLinearMap, hm, hA.trans_le (min_le_left _ _)⟩)
  have hn : ‖A‖ ≤ B + 1 := by
    have hdist : ‖A - L.toContinuousLinearMap‖ < 1 :=
      (dist_eq_norm A L.toContinuousLinearMap) ▸ hA.trans_le (min_le_right _ _)
    have hnorm := norm_le_norm_sub_add A L.toContinuousLinearMap
    linarith
  have hne : A.det ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hdet
    linarith
  let T := A.toContinuousLinearEquivOfDetNeZero hne
  refine ⟨T, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hne, ?_⟩
  exact hinv T hn hdet.le

end PlanarNikodym
