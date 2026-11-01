import PlanarNikodym.Analysis.Fourier.GlyzMomentBoxRescaling
import PlanarNikodym.Analysis.Fourier.GlyzTransverseCoordinates
import PlanarNikodym.Analysis.Fourier.GlyzAnisotropicConvolution

/-! Relative polar coordinates and exact densities for nested moment
intervals, allowing both their centers and their scales to change. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace PlanarNikodym

theorem det_glyzMomentAffineEuclidean (m : ℕ) (c κ : ℝ) (hκ : κ ≠ 0) :
    LinearMap.det (glyzMomentAffineEuclidean m c κ hκ).toLinearMap =
      κ ^ (m * (m + 1) / 2) := by
  change LinearMap.det
    ((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.comp
      ((glyzMomentAffineLinear m c κ hκ).toLinearMap.comp
        (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap)) = _
  rw [show LinearMap.det
      ((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.comp
        ((glyzMomentAffineLinear m c κ hκ).toLinearMap.comp
          (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap)) =
      LinearMap.det (glyzMomentAffineLinear m c κ hκ).toLinearMap from
        LinearMap.det_conj _ (EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearEquiv]
  change LinearMap.det (Matrix.toLin' (glyzMomentAffineMatrix m c κ)) = _
  rw [LinearMap.det_toLin', det_glyzMomentAffineMatrix]
  exact glyzMomentDensity_eq m κ

theorem det_glyzMomentFrequencyFrame (m : ℕ) (c δ : ℝ) (hδ : 0 < δ) :
    LinearMap.det (glyzMomentFrequencyFrame m c δ hδ).toLinearMap =
      δ ^ (m * (m + 1) / 2) *
        LinearMap.det (glyzMomentFrequencyFrame m 0 1 zero_lt_one).toLinearMap := by
  have hf : (glyzMomentFrequencyFrame m c δ hδ).toLinearMap =
      (glyzMomentAffineEuclidean m c δ hδ.ne').toLinearMap.comp
        (glyzMomentFrequencyFrame m 0 1 zero_lt_one).toLinearMap := by
    apply LinearMap.ext
    intro x
    change glyzMomentFrequencyFrame m c δ hδ x =
      glyzMomentAffineEuclidean m c δ hδ.ne' (glyzMomentFrequencyFrame m 0 1 zero_lt_one x)
    have h := congrArg (fun T : GlyzSpace m →L[ℝ] GlyzSpace m => T x)
      (glyzMomentFrequencyFrame_affine m c δ 0 1 hδ zero_lt_one)
    change glyzMomentAffineEuclidean m c δ hδ.ne'
      (glyzMomentFrequencyFrame m 0 1 zero_lt_one x) =
        glyzMomentFrequencyFrame m (c + δ * 0) (δ * 1) (mul_pos hδ zero_lt_one) x at h
    simpa only [mul_zero, add_zero, mul_one] using h.symm
  rw [hf, LinearMap.det_comp, det_glyzMomentAffineEuclidean]

theorem glyzMomentCoordinates_affine (m : ℕ) (c κ s δ : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (x : GlyzSpace m) :
    glyzBoxCoordinates (glyzMomentFrequencyFrame m (c + κ * s) (κ * δ)
      (mul_pos hκ hδ)) x =
    glyzBoxCoordinates (glyzMomentFrequencyFrame m s δ hδ)
      (glyzAdjointEquiv (glyzMomentAffineEuclidean m c κ hκ.ne') x) := by
  ext j
  rw [glyzBoxCoordinates_apply, glyzBoxCoordinates_apply, glyzAdjointEquiv_inner]
  have hf := congrArg (fun T : GlyzSpace m →L[ℝ] GlyzSpace m =>
    T (EuclideanSpace.basisFun (Fin m) ℝ j))
      (glyzMomentFrequencyFrame_affine m c κ s δ hκ hδ)
  exact congrArg (inner ℝ x) hf.symm

/-- In normalized coordinates the relative polar map contracts at least
by the length ratio, up to a constant depending only on dimension. -/
theorem exists_uniform_glyzMomentCoordinates_normalized (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ x : GlyzSpace m,
      ‖glyzBoxCoordinates (glyzMomentFrequencyFrame m s δ hδ) x‖ ≤
        D * δ * ‖glyzBoxCoordinates (glyzMomentFrequencyFrame m 0 1 zero_lt_one) x‖ := by
  obtain ⟨B, hB, hj⟩ := exists_uniform_glyzEuclideanJet_bound m
  let Q := (glyzAdjointEquiv (glyzMomentFrequencyFrame m 0 1 zero_lt_one)).trans
    (EuclideanSpace.equiv (Fin m) ℝ)
  let K := ‖Q.symm.toContinuousLinearMap‖
  have hK : 0 ≤ K := norm_nonneg _
  refine ⟨1 + B * K, by nlinarith, ?_⟩
  intro s hs δ hδ hδ1 x
  have hx : ‖x‖ ≤ K * ‖glyzBoxCoordinates (glyzMomentFrequencyFrame m 0 1 zero_lt_one) x‖ := by
    have h := Q.symm.toContinuousLinearMap.le_opNorm (Q x)
    change ‖Q.symm (Q x)‖ ≤ K * ‖Q x‖ at h
    rw [Q.symm_apply_apply] at h
    exact h
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [glyzBoxCoordinates_apply, glyzMomentFrequencyFrame_basis, inner_smul_right,
    norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos hδ _)]
  change δ ^ ((j : ℕ) + 1) * ‖inner ℝ x (glyzEuclideanJetBlock m m s j)‖ ≤ _
  have hp : δ ^ ((j : ℕ) + 1) ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ.le hδ1 (show 1 ≤ (j : ℕ) + 1 by omega)
  have hi := (norm_inner_le_norm (𝕜 := ℝ) x (glyzEuclideanJetBlock m m s j)).trans
    (mul_le_mul_of_nonneg_left (hj s hs j) (norm_nonneg x))
  calc
    _ ≤ δ * (‖x‖ * B) := mul_le_mul hp hi (norm_nonneg _) hδ.le
    _ ≤ δ * ((K * ‖glyzBoxCoordinates (glyzMomentFrequencyFrame m 0 1 zero_lt_one) x‖) * B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (by linarith)) hδ.le
    _ ≤ _ := by nlinarith [norm_nonneg (glyzBoxCoordinates (glyzMomentFrequencyFrame m 0 1 zero_lt_one) x)]

/-- Uniformity includes arbitrarily translated and arbitrarily large parent
intervals; only the relative center and relative scale are bounded. -/
theorem exists_uniform_glyzMomentCoordinates_nested (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (c κ s ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ),
      s ∈ Icc (-1 : ℝ) 1 → ρ ≤ 1 → ∀ x : GlyzSpace m,
      ‖glyzBoxCoordinates (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ)
        (mul_pos hκ hρ)) x‖ ≤
        D * ρ * ‖glyzBoxCoordinates (glyzMomentFrequencyFrame m c κ hκ) x‖ := by
  obtain ⟨D, hD, h⟩ := exists_uniform_glyzMomentCoordinates_normalized m
  refine ⟨D, hD, ?_⟩
  intro c κ s ρ hκ hρ hs hρ1 x
  rw [glyzMomentCoordinates_affine m c κ s ρ hκ hρ x]
  have hzero := glyzMomentCoordinates_affine m c κ 0 1 hκ zero_lt_one x
  simp only [mul_zero, add_zero, mul_one] at hzero
  rw [hzero]
  exact h s hs ρ hρ hρ1 _

end PlanarNikodym
