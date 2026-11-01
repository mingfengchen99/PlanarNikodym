import PlanarNikodym.Analysis.Fourier.GlyzDecayWeights
import PlanarNikodym.Analysis.Fourier.CoefficientDilation

/-! The canonical anisotropic convolution estimate of GLYZ v3, Appendix A.1.
The normalization is the actual determinant of the moment dilation. -/
noncomputable section
open MeasureTheory
namespace PlanarNikodym

def glyzMomentDensity (n : ℕ) (δ : ℝ) : ℝ :=
  ∏ j : Fin n, δ ^ ((j : ℕ) + 1)

def glyzMomentDilation (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0) : Base n ≃L[ℝ] Base n :=
  coefficientDilation (fun j : Fin n => δ ^ ((j : ℕ) + 1))
    (fun _ => pow_ne_zero _ hδ)

def glyzMomentWeight {n : ℕ} (A : ℕ) (δ : ℝ) (hδ : δ ≠ 0) (x : Base n) : ℝ :=
  glyzMomentDensity n δ * glyzDecayWeight A (glyzMomentDilation n δ hδ x)

theorem sum_moment_orders (n : ℕ) :
    (∑ j : Fin n, ((j : ℕ) + 1)) = n * (n + 1) / 2 := by
  have hs : (∑ j : Fin n, ((j : ℕ) + 1)) * 2 = n * (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      nlinarith
  omega

theorem glyzMomentDensity_eq (n : ℕ) (δ : ℝ) :
    glyzMomentDensity n δ = δ ^ (n * (n + 1) / 2) := by
  rw [glyzMomentDensity, Finset.prod_pow_eq_pow_sum, sum_moment_orders]

theorem glyzMomentDensity_pos (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < glyzMomentDensity n δ := by
  rw [glyzMomentDensity_eq]
  positivity

theorem norm_glyzMomentDilation_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (x : Base n) : ‖glyzMomentDilation n δ hδ.ne' x‖ ≤ δ * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖δ ^ ((i : ℕ) + 1) * x i‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos hδ _)]
  exact mul_le_mul
    (by simpa using pow_le_pow_of_le_one hδ.le hδ₁ (show 1 ≤ (i : ℕ) + 1 by omega))
    (norm_le_pi_norm x i) (norm_nonneg _) hδ.le

theorem continuous_glyzMomentWeight {n : ℕ} (A : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    Continuous (glyzMomentWeight (n := n) A δ hδ) :=
  continuous_const.mul ((continuous_glyzDecayWeight A).comp
    (glyzMomentDilation n δ hδ).continuous)

theorem glyzMomentWeight_pos {n : ℕ} (A : ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Base n) :
    0 < glyzMomentWeight A δ hδ.ne' x :=
  mul_pos (glyzMomentDensity_pos n hδ) (glyzDecayWeight_pos _ _)

theorem integrable_glyzMomentWeight {n A : ℕ} (hA : n < A) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (glyzMomentWeight (n := n) A δ hδ.ne') := by
  have hm : Integrable (glyzDecayWeight (n := n) A)
      (Measure.map (glyzMomentDilation n δ hδ.ne') volume) := by
    rw [glyzMomentDilation, map_coefficientDilation_volume]
    exact (integrable_glyzDecayWeight hA).smul_measure ENNReal.ofReal_ne_top
  exact (hm.comp_measurable (glyzMomentDilation n δ hδ.ne').continuous.measurable).const_mul _

/-- Normalization of the rescaled weight is exact and independent of scale. -/
theorem integral_glyzMomentWeight {n : ℕ} (A : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : Base n, glyzMomentWeight A δ hδ.ne' x) = ∫ x : Base n, glyzDecayWeight A x := by
  let T := glyzMomentDilation n δ hδ.ne'
  have hm : (∫ x, glyzDecayWeight A (T x)) =
      (glyzMomentDensity n δ)⁻¹ * ∫ x : Base n, glyzDecayWeight A x := by
    calc
      _ = ∫ y, glyzDecayWeight A y ∂Measure.map T volume :=
        (T.toHomeomorph.isClosedEmbedding.integral_map _).symm
      _ = _ := by
        rw [show Measure.map T volume =
          ENNReal.ofReal (|(glyzMomentDensity n δ)⁻¹|) • volume from
          map_coefficientDilation_volume _ _, integral_smul_measure,
          ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
          abs_of_pos (inv_pos.mpr (glyzMomentDensity_pos n hδ))]
  unfold glyzMomentWeight
  rw [integral_const_mul, hm, ← mul_assoc,
    mul_inv_cancel₀ (glyzMomentDensity_pos n hδ).ne', one_mul]

/-- Pointwise integrand domination; the decay threshold is exactly the
homogeneous dimension required by the corrected v3 statement. -/
theorem glyzMomentWeight_two_region {n A : ℕ} (hA : n * (n + 1) / 2 ≤ A)
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (x y : Base n) :
    glyzDecayWeight A (x - y) * glyzMomentWeight A δ hδ.ne' y ≤
      2 ^ A * glyzMomentWeight A δ hδ.ne' x *
        (glyzDecayWeight A (x - y) + glyzMomentWeight A δ hδ.ne' y) := by
  apply glyzDecayWeight_two_region (glyzMomentDilation n δ hδ.ne').toLinearMap hδ.le
    (glyzMomentDensity_pos n hδ).le
  · rw [glyzMomentDensity_eq]
    exact pow_le_pow_of_le_one hδ.le hδ₁ hA
  · exact norm_glyzMomentDilation_le n hδ hδ₁

/-- The uniform convolution bound of Appendix A.1, as an actual Lebesgue
integral. Both the integral and the constant are finite for A > n. -/
theorem integral_glyzMomentWeight_convolution_le {n A : ℕ} (hA : n < A)
    (hQ : n * (n + 1) / 2 ≤ A) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (x : Base n) :
    (∫ y, glyzDecayWeight A (x - y) * glyzMomentWeight A δ hδ.ne' y) ≤
      (2 ^ (A + 1) * ∫ y : Base n, glyzDecayWeight A y) *
        glyzMomentWeight A δ hδ.ne' x := by
  have hf : Integrable (fun y : Base n => glyzDecayWeight A (x - y)) :=
    ((integrable_glyzDecayWeight hA).comp_sub_right x).congr
      (Filter.Eventually.of_forall (fun y => by simp only [glyzDecayWeight, norm_sub_rev]))
  have hg := integrable_glyzMomentWeight hA hδ
  have hfint : (∫ y : Base n, glyzDecayWeight A (x - y)) =
      ∫ y : Base n, glyzDecayWeight A y := by
    calc
      _ = ∫ y : Base n, glyzDecayWeight A (y - x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change (max 1 ‖x - y‖ ^ A)⁻¹ = (max 1 ‖y - x‖ ^ A)⁻¹
          rw [norm_sub_rev x y]
      _ = _ := integral_sub_right_eq_self _ x
  have hprod : Integrable (fun y => glyzDecayWeight A (x - y) *
      glyzMomentWeight A δ hδ.ne' y) := by
    apply hg.mono' ((continuous_glyzDecayWeight A).comp (continuous_const.sub continuous_id)
      |>.mul (continuous_glyzMomentWeight A δ hδ.ne')).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      change |glyzDecayWeight A (x - y) * glyzMomentWeight A δ hδ.ne' y| ≤ _
      rw [abs_of_pos
        (mul_pos (glyzDecayWeight_pos _ _) (glyzMomentWeight_pos A hδ y))]
      exact mul_le_of_le_one_left (glyzMomentWeight_pos A hδ y).le
        (glyzDecayWeight_le_one A (x - y))
  calc
    _ ≤ ∫ y, 2 ^ A * glyzMomentWeight A δ hδ.ne' x *
        (glyzDecayWeight A (x - y) + glyzMomentWeight A δ hδ.ne' y) :=
      integral_mono hprod ((hf.add hg).const_mul _) (glyzMomentWeight_two_region hQ hδ hδ₁ x)
    _ = _ := by
      rw [integral_const_mul, integral_add hf hg, hfint,
        integral_glyzMomentWeight A hδ, pow_succ]
      ring

end PlanarNikodym
