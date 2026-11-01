import PlanarNikodym.Analysis.Fourier.GlyzMomentAffineJets

/-! Exact parabolic images of the actual moment-curve Fourier boxes.
This identifies the concrete affine map used by Fourier rescaling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
namespace PlanarNikodym

theorem glyzMomentFrequencyFrame_affine (m : ℕ) (c κ s δ : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) :
    (glyzMomentAffineEuclidean m c κ hκ.ne').toContinuousLinearMap.comp
      (glyzMomentFrequencyFrame m s δ hδ).toContinuousLinearMap =
        (glyzMomentFrequencyFrame m (c + κ * s) (κ * δ) (mul_pos hκ hδ)).toContinuousLinearMap := by
  have hl : ((glyzMomentAffineEuclidean m c κ hκ.ne').toContinuousLinearMap.comp
      (glyzMomentFrequencyFrame m s δ hδ).toContinuousLinearMap).toLinearMap =
      (glyzMomentFrequencyFrame m (c + κ * s) (κ * δ) (mul_pos hκ hδ)).toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
    intro j
    change glyzMomentAffineEuclidean m c κ hκ.ne'
      (glyzMomentFrequencyFrame m s δ hδ (EuclideanSpace.basisFun (Fin m) ℝ j)) =
        glyzMomentFrequencyFrame m (c + κ * s) (κ * δ) (mul_pos hκ hδ)
          (EuclideanSpace.basisFun (Fin m) ℝ j)
    rw [glyzMomentFrequencyFrame_basis, glyzMomentFrequencyFrame_basis]
    change glyzMomentAffineEuclidean m c κ hκ.ne'
      (δ ^ ((j : ℕ) + 1) • glyzEuclideanJetBlock m m s j) =
      (κ * δ) ^ ((j : ℕ) + 1) • glyzEuclideanJetBlock m m (c + κ * s) j
    rw [map_smul, glyzMomentAffineEuclidean_jet, smul_smul, mul_pow,
      mul_comm (δ ^ ((j : ℕ) + 1)) (κ ^ ((j : ℕ) + 1))]
  apply DFunLike.ext
  intro x
  exact LinearMap.congr_fun hl x

theorem glyzFrequencyBox_eq_image {m : ℕ} (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (a : GlyzSpace m) (R : ℝ) :
    glyzFrequencyBox L a R =
      (fun v : Base m => a + L ((EuclideanSpace.equiv (Fin m) ℝ).symm v)) '' closedBall 0 R := by
  ext ξ
  constructor
  · intro hξ
    refine ⟨(EuclideanSpace.equiv (Fin m) ℝ) (L.symm (ξ - a)), ?_, ?_⟩
    · simpa only [glyzFrequencyBox, mem_setOf_eq, mem_closedBall, dist_zero_right] using hξ
    · simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
      abel
  · rintro ⟨v, hv, rfl⟩
    change ‖(EuclideanSpace.equiv (Fin m) ℝ)
      (L.symm (a + L ((EuclideanSpace.equiv (Fin m) ℝ).symm v) - a))‖ ≤ R
    simpa only [add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply, mem_closedBall, dist_zero_right] using hv

theorem glyzMomentFrequencyBox_affine_image (m : ℕ) (c κ s δ : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) :
    (fun ξ => (EuclideanSpace.equiv (Fin m) ℝ).symm (glyzMomentCurve m c) +
      glyzMomentAffineEuclidean m c κ hκ.ne' ξ) '' glyzMomentFrequencyBox m s δ hδ =
        glyzMomentFrequencyBox m (c + κ * s) (κ * δ) (mul_pos hκ hδ) := by
  unfold glyzMomentFrequencyBox
  rw [glyzFrequencyBox_eq_image, glyzFrequencyBox_eq_image, ← Set.image_comp]
  apply congrArg (fun f : Base m → GlyzSpace m => f '' closedBall 0 1)
  funext v
  have hf := congrArg (fun A : GlyzSpace m →L[ℝ] GlyzSpace m =>
    A ((EuclideanSpace.equiv (Fin m) ℝ).symm v))
      (glyzMomentFrequencyFrame_affine m c κ s δ hκ hδ)
  change glyzMomentAffineEuclidean m c κ hκ.ne'
    (glyzMomentFrequencyFrame m s δ hδ ((EuclideanSpace.equiv (Fin m) ℝ).symm v)) = _ at hf
  change _ + glyzMomentAffineEuclidean m c κ hκ.ne' (_ + _) = _ + _
  rw [map_add, hf, glyzMomentAffineEuclidean_curve m c κ s hκ.ne']
  abel

end PlanarNikodym
