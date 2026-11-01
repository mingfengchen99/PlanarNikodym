import PlanarNikodym.Analysis.Fourier.GlyzTaylorMomentModel

/-! Exact affine identification of Taylor Fourier boxes with the actual
moment-curve boxes, including the derivative-scaled generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped BigOperators
namespace PlanarNikodym

theorem glyzMomentFrequencyFrame_coordinates (l : ℕ) (s δ : ℝ) (hδ : 0 < δ) (v : Base l) :
    glyzMomentFrequencyFrame l s δ hδ ((EuclideanSpace.equiv (Fin l) ℝ).symm v) =
      ∑ j : Fin l, (δ ^ ((j : ℕ) + 1) * v j) • glyzEuclideanJetBlock l l s j := by
  have hv : (EuclideanSpace.equiv (Fin l) ℝ).symm v =
      ∑ j : Fin l, v j • EuclideanSpace.basisFun (Fin l) ℝ j := by
    exact ((EuclideanSpace.basisFun (Fin l) ℝ).toBasis.sum_repr _).symm
  rw [hv, map_sum]
  simp_rw [map_smul, glyzMomentFrequencyFrame_basis, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl

theorem glyzMomentFrequencyBox_eq_generators (l : ℕ) (s δ : ℝ) (hδ : 0 < δ) :
    glyzMomentFrequencyBox l s δ hδ =
      (fun v : Base l => (EuclideanSpace.equiv (Fin l) ℝ).symm (glyzMomentCurve l s) +
        ∑ j : Fin l, (δ ^ ((j : ℕ) + 1) * v j) • glyzEuclideanJetBlock l l s j) ''
          {v : Base l | ∀ j, |v j| ≤ 1} := by
  rw [glyzMomentFrequencyBox, glyzFrequencyBox_eq_image]
  have hs : closedBall (0 : Base l) 1 = {v : Base l | ∀ j, |v j| ≤ 1} := by
    ext v
    simp only [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one,
      Real.norm_eq_abs, mem_setOf_eq]
  rw [hs]
  apply congrArg (fun f : Base l → GlyzSpace l => f '' {v | ∀ j, |v j| ≤ 1})
  funext v
  rw [glyzMomentFrequencyFrame_coordinates]

theorem glyzTaylorCurveBox_eq_affine_momentBox {l : ℕ}
    (γ : ℝ → GlyzSpace l) (a s δ : ℝ) (hδ : 0 < δ)
    (L : GlyzSpace l ≃L[ℝ] GlyzSpace l)
    (hL : L.toContinuousLinearMap = glyzCurveJetOperator γ a) :
    glyzCurveBox (glyzTaylorCurve γ l a) l s δ =
      (fun ξ => γ a + glyzTaylorMomentLinear L ξ) '' glyzMomentFrequencyBox l (s - a) δ hδ := by
  rw [glyzMomentFrequencyBox_eq_generators, ← Set.image_comp]
  unfold glyzCurveBox
  apply congrArg (fun f : Base l → GlyzSpace l => f '' {v | ∀ j, |v j| ≤ 1})
  funext v
  exact glyzCurveBoxPoint_taylor_affine_moment γ a s δ L hL v

end PlanarNikodym
