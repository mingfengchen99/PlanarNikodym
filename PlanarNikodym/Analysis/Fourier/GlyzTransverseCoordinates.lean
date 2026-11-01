import PlanarNikodym.Analysis.Fourier.GlyzProjectedCoordinates

/-! Uniform smallness of the actual polar coordinates on the
annihilator of the first r moment jets, at the scale δ^(r+1). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Submodule MeasureTheory
namespace PlanarNikodym

theorem exists_uniform_glyzEuclideanJet_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ j : Fin m,
      ‖glyzEuclideanJetBlock m m t j‖ ≤ D := by
  have h (j : Fin m) : ∃ C : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖glyzEuclideanJetBlock m m t j‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn
      (continuous_glyzEuclideanJetBlock m m j).continuousOn
  choose C hC using h
  refine ⟨1 + ∑ j : Fin m, |C j|,
    le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => abs_nonneg (C j)), ?_⟩
  intro t ht j
  apply (hC j t ht).trans
  have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin m => |C i|)
    (fun i _ => abs_nonneg (C i)) (Finset.mem_univ j)
  linarith [le_abs_self (C j)]

theorem glyzMomentCoordinates_transverse_bound {l r : ℕ} {D t δ : ℝ}
    (hD : 0 ≤ D) (hjet : ∀ j : Fin (l + r), ‖glyzEuclideanJetBlock (l + r) (l + r) t j‖ ≤ D)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (z : (glyzEuclideanTangentSpace (l + r) r t)ᗮ) :
    ‖glyzBoxCoordinates (glyzMomentFrequencyFrame (l + r) t δ hδ) z‖ ≤
      D * δ ^ (r + 1) * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [glyzBoxCoordinates_apply, glyzMomentFrequencyFrame_basis, inner_smul_right,
    norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos hδ _)]
  change δ ^ ((j : ℕ) + 1) * ‖inner ℝ (z : GlyzSpace (l + r))
    (glyzEuclideanJetBlock (l + r) (l + r) t j)‖ ≤ _
  by_cases hj : (j : ℕ) < r
  · have hm : glyzEuclideanJetBlock (l + r) (l + r) t j ∈
        glyzEuclideanTangentSpace (l + r) r t := by
      exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    rw [Submodule.inner_left_of_mem_orthogonal hm z.property, norm_zero, mul_zero]
    positivity
  · have hp : δ ^ ((j : ℕ) + 1) ≤ δ ^ (r + 1) :=
      pow_le_pow_of_le_one hδ.le hδ1 (by omega)
    have hi := (norm_inner_le_norm (𝕜 := ℝ) (z : GlyzSpace (l + r))
      (glyzEuclideanJetBlock (l + r) (l + r) t j)).trans
        (mul_le_mul_of_nonneg_left (hjet j) (norm_nonneg _))
    apply (mul_le_mul hp hi (norm_nonneg _) (pow_pos hδ _).le).trans_eq
    change δ ^ (r + 1) * (‖z‖ * D) = _
    ring

def glyzTransverseParameterization (l r : ℕ) (t : ℝ) : Base l →L[ℝ] GlyzSpace (l + r) :=
  (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL.comp
    ((glyzOrthogonalCoordinates l r t).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (EuclideanSpace.equiv (Fin l) ℝ).symm.toContinuousLinearMap)

theorem exists_uniform_glyzTransverse_coordinates (l r : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ z : Base l,
      ‖glyzBoxCoordinates (glyzMomentFrequencyFrame (l + r) t δ hδ)
        (glyzTransverseParameterization l r t z)‖ ≤ D * δ ^ (r + 1) * ‖z‖ := by
  obtain ⟨D, hD, hj⟩ := exists_uniform_glyzEuclideanJet_bound (l + r)
  let K := ‖(EuclideanSpace.equiv (Fin l) ℝ).symm.toContinuousLinearMap‖
  have hK : 0 ≤ K := norm_nonneg _
  refine ⟨D * (K + 1), by nlinarith, ?_⟩
  intro t ht δ hδ hδ1 z
  have h := glyzMomentCoordinates_transverse_bound (by linarith : 0 ≤ D) (hj t ht) hδ hδ1
    ((glyzOrthogonalCoordinates l r t).symm ((EuclideanSpace.equiv (Fin l) ℝ).symm z))
  change ‖glyzBoxCoordinates (glyzMomentFrequencyFrame (l + r) t δ hδ)
    (glyzTransverseParameterization l r t z)‖ ≤ _ at h
  rw [LinearIsometryEquiv.norm_map] at h
  apply h.trans
  have hn := (EuclideanSpace.equiv (Fin l) ℝ).symm.toContinuousLinearMap.le_opNorm z
  have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ D * δ ^ (r + 1) by positivity)
  apply hmul.trans
  calc
    _ ≤ D * δ ^ (r + 1) * ((K + 1) * ‖z‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) (norm_nonneg z))
        (by positivity)
    _ = _ := by ring

end PlanarNikodym
