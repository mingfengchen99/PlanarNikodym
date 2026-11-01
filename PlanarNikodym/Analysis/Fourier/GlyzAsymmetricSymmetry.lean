import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants

/-! Exact interchange of the two actual parent intervals, including
their polar measures, critical-power split, and optimal constants. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyzDyadicSeparated_symm {n n' i j : ℕ} (h : GlyzDyadicSeparated n n' i j) :
    GlyzDyadicSeparated n' n j i := by
  simpa only [GlyzDyadicSeparated, add_comm (glyzDyadicScale n'),
    abs_sub_comm] using h

theorem glyzDyadicBilinearValue_symm (m A N n n' : ℕ) (p : ℝ≥0) (a : ℝ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) :
    glyzDyadicBilinearValue m A N n' n p ((p : ℝ) - a) f j i =
      glyzDyadicBilinearValue m A N n n' p a f i j := by
  unfold glyzDyadicBilinearValue
  rw [sub_sub_cancel, glyzWeightedBilinear_symm]

theorem glyzDyadicBilinearEnergy_symm (m N n n' : ℕ) (p : ℝ≥0) (a : ℝ)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) :
    glyzDyadicBilinearEnergy m N n' n p ((p : ℝ) - a) f j i =
      glyzDyadicBilinearEnergy m N n n' p a f i j := by
  unfold glyzDyadicBilinearEnergy
  rw [sub_sub_cancel, mul_comm]

theorem glyz_asymmetric_integral_bound_symm {m A N n n' : ℕ} {p : ℝ≥0} {a C : ℝ}
    (hC : GlyzAsymmetricIntegralBound m A N n n' p a C) :
    GlyzAsymmetricIntegralBound m A N n' n p ((p : ℝ) - a) C := by
  refine ⟨hC.1, fun f hf i hi j hj hs => ?_⟩
  rw [glyzDyadicBilinearValue_symm, glyzDyadicBilinearEnergy_symm]
  exact hC.2 f hf j hj i hi (glyzDyadicSeparated_symm hs)

theorem glyz_asymmetric_integral_bound_symm_iff
    (m A N n n' : ℕ) (p : ℝ≥0) (a C : ℝ) :
    GlyzAsymmetricIntegralBound m A N n' n p ((p : ℝ) - a) C ↔
      GlyzAsymmetricIntegralBound m A N n n' p a C := by
  constructor
  · intro h
    simpa only [sub_sub_cancel] using glyz_asymmetric_integral_bound_symm h
  · exact glyz_asymmetric_integral_bound_symm

theorem glyzAsymmetricIntegralConstant_symm
    (m A N n n' : ℕ) (p : ℝ≥0) (a : ℝ) :
    glyzAsymmetricIntegralConstant m A N n' n p ((p : ℝ) - a) =
      glyzAsymmetricIntegralConstant m A N n n' p a := by
  unfold glyzAsymmetricIntegralConstant
  congr 1
  ext C
  exact glyz_asymmetric_integral_bound_symm_iff m A N n n' p a C

theorem glyz_admissible_asymmetric_loss_symm_iff (m A : ℕ) (p : ℝ≥0)
    (a alpha beta e : ℝ) :
    GlyzAdmissibleAsymmetricLoss m A p ((p : ℝ) - a) beta alpha e ↔
      GlyzAdmissibleAsymmetricLoss m A p a alpha beta e := by
  unfold GlyzAdmissibleAsymmetricLoss
  simp only [glyzAsymmetricIntegralConstant_symm]

theorem glyzOptimalAsymmetricLoss_symm (m A : ℕ) (p : ℝ≥0)
    (a alpha beta : ℝ) :
    glyzOptimalAsymmetricLoss m A p ((p : ℝ) - a) beta alpha =
      glyzOptimalAsymmetricLoss m A p a alpha beta := by
  unfold glyzOptimalAsymmetricLoss
  congr 1
  ext e
  exact glyz_admissible_asymmetric_loss_symm_iff m A p a alpha beta e

end PlanarNikodym
