import PlanarNikodym.Analysis.Fourier.GlyzProjectedCoordinates
import PlanarNikodym.Analysis.Fourier.GlyzUniformFrameInverse

/-! Actual derivative frames of the projected curves and their uniformly
bounded inverses. No continuous choice of orthonormal bases is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped BigOperators
namespace PlanarNikodym

def glyzCurveJetOperator {l : ℕ} (γ : ℝ → GlyzSpace l) (s : ℝ) :
    GlyzSpace l →L[ℝ] GlyzSpace l :=
  (EuclideanSpace.basisFun (Fin l) ℝ).toBasis.constrL
    (fun j : Fin l => iteratedDeriv ((j : ℕ) + 1) γ s)

theorem glyzCurveJetOperator_apply {l : ℕ} (γ : ℝ → GlyzSpace l) (s : ℝ)
    (v : GlyzSpace l) :
    glyzCurveJetOperator γ s v =
      ∑ j : Fin l, v j • iteratedDeriv ((j : ℕ) + 1) γ s := by
  simp only [glyzCurveJetOperator, Module.Basis.constrL_apply]
  rfl

theorem glyzCurveJetOperator_basis {l : ℕ} (γ : ℝ → GlyzSpace l) (s : ℝ) (j : Fin l) :
    glyzCurveJetOperator γ s (EuclideanSpace.basisFun (Fin l) ℝ j) =
      iteratedDeriv ((j : ℕ) + 1) γ s := by
  exact Module.Basis.constrL_basis _ _ _

theorem det_glyzCurveJetOperator (l r : ℕ) (t s : ℝ) :
    (glyzCurveJetOperator (glyzCoordinateCurve l r t) s).det =
      (glyzCoordinateTorsionMatrix l r t s).det := by
  change LinearMap.det (glyzCurveJetOperator (glyzCoordinateCurve l r t) s).toLinearMap = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin l) ℝ).toBasis]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  change (glyzCurveJetOperator (glyzCoordinateCurve l r t) s
    (EuclideanSpace.basisFun (Fin l) ℝ j)) i = _
  rw [glyzCurveJetOperator_basis]
  rfl

theorem norm_glyzCurveJetOperator_le {l : ℕ} (γ : ℝ → GlyzSpace l) (s : ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ j : Fin l, ‖iteratedDeriv ((j : ℕ) + 1) γ s‖ ≤ C) :
    ‖glyzCurveJetOperator γ s‖ ≤ (l : ℝ) * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [glyzCurveJetOperator_apply]
  calc
    _ ≤ ∑ j : Fin l, ‖v j • iteratedDeriv ((j : ℕ) + 1) γ s‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin l, ‖v‖ * C := Finset.sum_le_sum fun j _ => by
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v j) (hjet j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

theorem exists_uniform_glyzCoordinateCurve_inverse (l r : ℕ) {ν : ℝ} (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ separatedMixedCenters ν,
      ∃ L : GlyzSpace l ≃L[ℝ] GlyzSpace l,
        L.toContinuousLinearMap = glyzCurveJetOperator (glyzCoordinateCurve l r z.2) z.1 ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ C := by
  obtain ⟨b, B, hb, hB, _, hder, hdet⟩ :=
    exists_uniform_glyzCoordinateCurve_certificate l r l hν
  obtain ⟨C, hC, hinv⟩ := exists_uniform_glyz_frame_inverse (E := GlyzSpace l) hb ((l : ℝ) * B)
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hd : (glyzCurveJetOperator (glyzCoordinateCurve l r z.2) z.1).det ≠ 0 := by
    rw [det_glyzCurveJetOperator]
    intro he
    have h := hdet z hz
    rw [he, abs_zero] at h
    exact (not_le_of_gt hb) h
  let L := (glyzCurveJetOperator (glyzCoordinateCurve l r z.2) z.1).toContinuousLinearEquivOfDetNeZero hd
  refine ⟨L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hd, ?_⟩
  apply hinv L
  · change ‖glyzCurveJetOperator (glyzCoordinateCurve l r z.2) z.1‖ ≤ _
    apply norm_glyzCurveJetOperator_le _ _ hB.le
    intro j
    exact hder z.2 z.1 hz.1 ((j : ℕ) + 1) j.isLt
  · change b ≤ |(glyzCurveJetOperator (glyzCoordinateCurve l r z.2) z.1).det|
    rw [det_glyzCurveJetOperator]
    exact hdet z hz

end PlanarNikodym
