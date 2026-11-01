import PlanarNikodym.Analysis.Fourier.GlyzSubspaceConvolution
import PlanarNikodym.Analysis.Fourier.GlyzPolarBilinearMeasure

/-! Weighted subspace convolution for actual volume-normalized polar
boxes, with an explicit operator distortion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace PlanarNikodym

theorem glyzPolarWeight_shift {m : ℕ} (A : ℕ)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (x y : GlyzSpace m) :
    glyzPolarWeight A L (x - y) ≤
      2 ^ A * glyzPolarWeight A L x * max (1 : ℝ) ‖glyzBoxCoordinates L y‖ ^ A := by
  have h := glyzDecayWeight_shift A (glyzBoxCoordinates L x) (glyzBoxCoordinates L y)
  have he : glyzBoxCoordinates L (x - y) = glyzBoxCoordinates L x - glyzBoxCoordinates L y := by
    simp only [glyzBoxCoordinates, map_sub]
  rw [← he] at h
  have h' := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L.toLinearMap| by positivity)
  simpa only [glyzPolarWeight, glyzBoxWeight, mul_assoc, mul_comm, mul_left_comm] using h'

theorem glyzPolarWeight_subspace_pointwise {m l : ℕ} (A B : ℕ)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (S : Base l →L[ℝ] GlyzSpace m)
    {D b : ℝ} (hD : 1 ≤ D) (hb : 0 < b)
    (hS : ∀ z, ‖glyzBoxCoordinates L (S z)‖ ≤ D * b * ‖z‖)
    (x : GlyzSpace m) (z : Base l) :
    glyzDecayWeight (A + B) (b • z) * glyzPolarWeight A L (x - S z) ≤
      ((2 * D) ^ A * glyzPolarWeight A L x) * glyzDecayWeight B (b • z) := by
  let q := max (1 : ℝ) ‖b • z‖
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hq1 : 1 ≤ q := le_max_left _ _
  have hD0 : 0 < D := by linarith
  have hmax : max (1 : ℝ) ‖glyzBoxCoordinates L (S z)‖ ≤ D * q := by
    apply max_le
    · nlinarith
    · have he : b * ‖z‖ = ‖b • z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
      apply (hS z).trans
      rw [mul_assoc, he]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) hD0.le
  have h := (glyzPolarWeight_shift A L x (S z)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmax A)
      (mul_nonneg (by positivity) (glyzPolarWeight_pos A L x).le))
  have h' := mul_le_mul_of_nonneg_left h (glyzDecayWeight_pos (A + B) (b • z)).le
  apply h'.trans_eq
  change (q ^ (A + B))⁻¹ * (2 ^ A * glyzPolarWeight A L x * (D * q) ^ A) =
    (2 * D) ^ A * glyzPolarWeight A L x * (q ^ B)⁻¹
  rw [pow_add, mul_inv, mul_pow, mul_pow]
  field_simp

/-- The distortion `D` is uniform geometric data, not a scale loss. -/
theorem integral_glyzPolarWeight_subspace_le {m l B : ℕ} (A : ℕ) (hB : l < B)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (S : Base l →L[ℝ] GlyzSpace m)
    {D b : ℝ} (hD : 1 ≤ D) (hb : 0 < b)
    (hS : ∀ z, ‖glyzBoxCoordinates L (S z)‖ ≤ D * b * ‖z‖) (x : GlyzSpace m) :
    (∫ z : Base l, glyzIsotropicWeight (A + B) b z * glyzPolarWeight A L (x - S z)) ≤
      ((2 * D) ^ A * ∫ z : Base l, glyzDecayWeight B z) * glyzPolarWeight A L x := by
  have hg := integrable_glyzIsotropicWeight hB hb
  have hdom (z : Base l) :
      glyzIsotropicWeight (A + B) b z * glyzPolarWeight A L (x - S z) ≤
        ((2 * D) ^ A * glyzPolarWeight A L x) * glyzIsotropicWeight B b z := by
    simpa only [glyzIsotropicWeight, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left (glyzPolarWeight_subspace_pointwise A B L S hD hb hS x z)
        (pow_pos hb l).le
  have hprod : Integrable (fun z : Base l => glyzIsotropicWeight (A + B) b z *
      glyzPolarWeight A L (x - S z)) := by
    apply (hg.const_mul ((2 * D) ^ A * glyzPolarWeight A L x)).mono'
      (by
        apply Continuous.aestronglyMeasurable
        unfold glyzIsotropicWeight
        exact (continuous_const.mul ((continuous_glyzDecayWeight (A + B)).comp
          (continuous_const.smul continuous_id))).mul
          ((continuous_glyzPolarWeight A L).comp (continuous_const.sub S.continuous)))
    exact Filter.Eventually.of_forall fun z => by
      have hp : 0 < glyzIsotropicWeight (A + B) b z :=
        mul_pos (pow_pos hb l) (glyzDecayWeight_pos _ _)
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos hp (glyzPolarWeight_pos _ _ _))]
      exact hdom z
  calc
    _ ≤ ∫ z : Base l, ((2 * D) ^ A * glyzPolarWeight A L x) * glyzIsotropicWeight B b z :=
      integral_mono hprod (hg.const_mul _) hdom
    _ = _ := by rw [integral_const_mul, integral_glyzIsotropicWeight B hb]; ring

theorem lintegral_glyzPolarWeight_subspace_le {m l B : ℕ} (A : ℕ) (hB : l < B)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (S : Base l →L[ℝ] GlyzSpace m)
    {D b : ℝ} (hD : 1 ≤ D) (hb : 0 < b)
    (hS : ∀ z, ‖glyzBoxCoordinates L (S z)‖ ≤ D * b * ‖z‖) (x : GlyzSpace m) :
    (∫⁻ z : Base l, ENNReal.ofReal (glyzIsotropicWeight (A + B) b z) *
      ENNReal.ofReal (glyzPolarWeight A L (x - S z))) ≤
      ENNReal.ofReal ((2 * D) ^ A * ∫ z : Base l, glyzDecayWeight B z) *
        ENNReal.ofReal (glyzPolarWeight A L x) := by
  have hD0 : 0 < D := by linarith
  have hW : 0 ≤ (2 * D) ^ A * glyzPolarWeight A L x :=
    mul_nonneg (by positivity) (glyzPolarWeight_pos _ _ _).le
  have hmass : (∫⁻ z : Base l, ENNReal.ofReal (glyzIsotropicWeight B b z)) =
      ENNReal.ofReal (∫ z : Base l, glyzDecayWeight B z) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_glyzIsotropicWeight hB hb)
      (Filter.Eventually.of_forall fun z => (mul_pos (pow_pos hb l) (glyzDecayWeight_pos _ _)).le),
      integral_glyzIsotropicWeight B hb]
  calc
    _ ≤ ∫⁻ z : Base l, ENNReal.ofReal ((2 * D) ^ A * glyzPolarWeight A L x) *
        ENNReal.ofReal (glyzIsotropicWeight B b z) := by
      apply lintegral_mono
      intro z
      dsimp only
      have hp : 0 ≤ glyzIsotropicWeight (A + B) b z :=
        (mul_pos (pow_pos hb l) (glyzDecayWeight_pos _ _)).le
      rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hW]
      apply ENNReal.ofReal_le_ofReal
      simpa only [glyzIsotropicWeight, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left (glyzPolarWeight_subspace_pointwise A B L S hD hb hS x z)
          (pow_pos hb l).le
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmass,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * D) ^ A),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * D) ^ A)]
      ring

end PlanarNikodym
