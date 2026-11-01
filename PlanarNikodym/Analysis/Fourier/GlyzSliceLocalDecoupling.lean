import PlanarNikodym.Analysis.Fourier.GlyzSliceCoordinates
import PlanarNikodym.Analysis.Fourier.GlyzFlexibleCurveLocalization
import PlanarNikodym.Analysis.Fourier.GlyzRadialCoordinateComparison

/-! Actual transverse local decoupling for ambient moment-curve Fourier
pieces. The only analytic induction premise is the lower-dimensional
moment optimal loss; the slice estimate itself is proved here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem exists_uniform_glyz_slice_local_decoupling
    (l r A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0) (L : ℝ) (hL : 0 < L)
    {ν R ε : ℝ} (hν : 0 < ν) (hR : 0 < R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t b : ℝ), 0 < b →
      b ≤ L * glyzDyadicScale N ^ l → ∀ (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace (l + r)) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace (l + r) → ℂ)) ⊆
        glyzFrequencyBox
          (glyzMomentFrequencyFrame (l + r) (glyzDyadicCenter N j)
            (glyzDyadicScale N) (glyzDyadicScale_pos N))
          ((EuclideanSpace.equiv (Fin (l + r)) ℝ).symm
            (glyzMomentCurve (l + r) (glyzDyadicCenter N j))) R) →
      ∀ x : GlyzSpace (l + r),
      glyzSubspaceAverage
        (glyzBallMeasure ((glyzEuclideanTangentSpace (l + r) r t)ᗮ) b⁻¹)
        (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL
        (fun y => ‖(∑ j ∈ I, f j) y‖ₑ ^ (p : ℝ)) x ≤
      ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
        (∑ j ∈ I, (glyzSubspaceAverage
          (glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t) A b)
          (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL
          (fun y => ‖f j y‖ₑ ^ (p : ℝ)) x) ^ (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  classical
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨Q, hQ, hsupport⟩ := exists_uniform_glyzProjectedSliceAt_support l r hν hR
  obtain ⟨B, hB, hlocal⟩ := glyz_controlled_curve_flexible_local_of_moment_optimal_zero
    l r A hp hη L hL hν hQ hε
  obtain ⟨K, hK, hdensity⟩ := exists_uniform_glyz_radial_coordinate_comparison l A
    (L := 1) le_rfl
  refine ⟨B * K, mul_pos hB hK, fun N t b hb hbscale I f hI hsep hf x => ?_⟩
  let g : ℕ → SchwartzMap (GlyzSpace l) ℂ := fun j => glyzProjectedSliceAt l r t x (f j)
  have hδ1 : glyzDyadicScale N ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hg := hlocal N t I g b hb hbscale hI hsep (fun j hj =>
    hsupport (glyzDyadicCenter N j, t) (hsep j hj) _ (glyzDyadicScale_pos N)
      hδ1 (f j) x (hf j hj))
  have hn := glyz_normalize_local_decoupling I g (inv_pos.mpr hb) hp0
    (fun y => ENNReal.ofReal (glyzNormWeight A (b • y)))
    (ENNReal.ofReal (B * (2 : ℝ) ^ (ε * N))) hg
  have hi (j : ℕ) :
      (∫⁻ y, ‖g j y‖ₑ ^ (p : ℝ) *
        ((volume (closedBall (0 : GlyzSpace l) b⁻¹))⁻¹ *
          ENNReal.ofReal (glyzNormWeight A (b • y)))) ≤
        ENNReal.ofReal K * (∫⁻ y, ‖g j y‖ₑ ^ (p : ℝ) * ENNReal.ofReal
          (glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) y))) := by
    calc
      _ ≤ ∫⁻ y, ‖g j y‖ₑ ^ (p : ℝ) * (ENNReal.ofReal K * ENNReal.ofReal
          (glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) y))) :=
        lintegral_mono fun y => mul_le_mul' le_rfl (hdensity b b hb hb (by simp) y)
      _ = _ := by
        simp_rw [mul_left_comm (‖g j _‖ₑ ^ (p : ℝ)) (ENNReal.ofReal K)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hsum := ENNReal.rpow_le_rpow (Finset.sum_le_sum (fun j (_hj : j ∈ I) =>
    ENNReal.rpow_le_rpow (hi j) (by positivity : (0 : ℝ) ≤ 2 / p)))
      (by positivity : (0 : ℝ) ≤ (p : ℝ) / 2)
  rw [glyz_power_square_sum_mul I _ (ENNReal.ofReal K) hp0] at hsum
  have hfinal := hn.trans (mul_le_mul' le_rfl hsum)
  have he : ENNReal.ofReal (B * (2 : ℝ) ^ (ε * N)) * ENNReal.ofReal K =
      ENNReal.ofReal (B * K * (2 : ℝ) ^ (ε * N)) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ B * (2 : ℝ) ^ (ε * N))]
    congr 1
    ring
  rw [← mul_assoc, he] at hfinal
  change (∫⁻ y, ‖(∑ j ∈ I, glyzProjectedSliceAt l r t x (f j)) y‖ₑ ^ (p : ℝ)
    ∂glyzBallMeasure (GlyzSpace l) b⁻¹) ≤ _ at hfinal
  rw [← glyzProjectedSliceAt_sum, glyzProjectedSliceAt_ball_average] at hfinal
  simpa only [g, glyzProjectedSliceAt_coordinate_average] using hfinal

end PlanarNikodym
