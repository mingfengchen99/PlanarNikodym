import PlanarNikodym.Analysis.Fourier.GlyzAnisotropicConvolution
import PlanarNikodym.Analysis.Fourier.GlyzMomentJets

/-! Weighted convolution along the canonical transverse subspace.
We use the sufficient exponent A' = A + m, allowed by GLYZ v3. -/
noncomputable section
open MeasureTheory
namespace PlanarNikodym

theorem glyzDecayWeight_shift {n : ℕ} (A : ℕ) (x y : Base n) :
    glyzDecayWeight A (x - y) ≤
      2 ^ A * glyzDecayWeight A x * max (1 : ℝ) ‖y‖ ^ A := by
  let u := max (1 : ℝ) ‖x - y‖
  let v := max (1 : ℝ) ‖y‖
  let q := max (1 : ℝ) ‖x‖
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hv : 0 < v := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hu1 : 1 ≤ u := le_max_left _ _
  have hv1 : 1 ≤ v := le_max_left _ _
  have hb : q ≤ 2 * u * v := by
    apply max_le
    · nlinarith [mul_le_mul hu1 hv1 (by norm_num : (0 : ℝ) ≤ 1) hu.le]
    · have ht : ‖x‖ ≤ u + v := by
        calc
          ‖x‖ = ‖x - y + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
          _ ≤ u + v := add_le_add (le_max_right _ _) (le_max_right _ _)
      have h1 := mul_le_mul_of_nonneg_left hv1 hu.le
      have h2 := mul_le_mul_of_nonneg_right hu1 hv.le
      nlinarith
  have hp := pow_le_pow_left₀ hq.le hb A
  have hd : (1 : ℝ) / u ^ A ≤ (2 ^ A * v ^ A) / q ^ A :=
    (div_le_div_iff₀ (pow_pos hu A) (pow_pos hq A)).mpr (by
      simpa only [mul_pow, one_mul, mul_assoc, mul_comm, mul_left_comm] using hp)
  change (u ^ A)⁻¹ ≤ 2 ^ A * (q ^ A)⁻¹ * v ^ A
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hd

def glyzIsotropicWeight {l : ℕ} (A : ℕ) (b : ℝ) (z : Base l) : ℝ :=
  b ^ l * glyzDecayWeight A (b • z)

theorem integrable_glyzIsotropicWeight {l B : ℕ} (hB : l < B) {b : ℝ} (hb : 0 < b) :
    Integrable (glyzIsotropicWeight (l := l) B b) := by
  let T := coefficientDilation (fun _ : Fin l => b) (fun _ => hb.ne')
  have hm : Integrable (glyzDecayWeight (n := l) B) (Measure.map T volume) := by
    rw [show Measure.map T volume = ENNReal.ofReal (|(b ^ l)⁻¹|) • volume from by
      simpa using map_coefficientDilation_volume (fun _ : Fin l => b) (fun _ => hb.ne')]
    exact (integrable_glyzDecayWeight hB).smul_measure ENNReal.ofReal_ne_top
  exact (hm.comp_measurable T.continuous.measurable).const_mul _

theorem integral_glyzIsotropicWeight {l : ℕ} (B : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ z : Base l, glyzIsotropicWeight B b z) = ∫ z : Base l, glyzDecayWeight B z := by
  let T := coefficientDilation (fun _ : Fin l => b) (fun _ => hb.ne')
  have hm : (∫ z, glyzDecayWeight B (T z)) =
      (b ^ l)⁻¹ * ∫ z : Base l, glyzDecayWeight B z := by
    calc
      _ = ∫ z, glyzDecayWeight B z ∂Measure.map T volume :=
        (T.toHomeomorph.isClosedEmbedding.integral_map _).symm
      _ = _ := by
        rw [show Measure.map T volume = ENNReal.ofReal (|(b ^ l)⁻¹|) • volume from by
          simpa using map_coefficientDilation_volume (fun _ : Fin l => b) (fun _ => hb.ne'),
          integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
          abs_of_pos (inv_pos.mpr (pow_pos hb l))]
  unfold glyzIsotropicWeight
  change (∫ z, b ^ l * glyzDecayWeight B (T z)) = _
  rw [integral_const_mul, hm, ← mul_assoc, mul_inv_cancel₀ (pow_pos hb l).ne', one_mul]

theorem glyzDecayWeight_subspace_pointwise {l n : ℕ} (A B : ℕ)
    (T : Base n →ₗ[ℝ] Base n) (S : Base l →ₗ[ℝ] Base n)
    {b : ℝ} (hb : 0 < b) (hTS : ∀ z, ‖T (S z)‖ ≤ b * ‖z‖)
    (x : Base n) (z : Base l) :
    glyzDecayWeight (A + B) (b • z) * glyzDecayWeight A (T (x - S z)) ≤
      (2 ^ A * glyzDecayWeight A (T x)) * glyzDecayWeight B (b • z) := by
  have hs := glyzDecayWeight_shift A (T x) (T (S z))
  rw [← map_sub] at hs
  have hg : max (1 : ℝ) ‖T (S z)‖ ≤ max (1 : ℝ) ‖b • z‖ := by
    apply max_le_max le_rfl
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hb] using hTS z
  have hq : 0 < max (1 : ℝ) ‖b • z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hw : max (1 : ℝ) ‖T (S z)‖ ^ A * glyzDecayWeight (A + B) (b • z) ≤
      glyzDecayWeight B (b • z) := by
    calc
      _ ≤ max (1 : ℝ) ‖b • z‖ ^ A * glyzDecayWeight (A + B) (b • z) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hg A)
          (glyzDecayWeight_pos _ _).le
      _ = _ := by
        unfold glyzDecayWeight
        rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_pos hq A).ne', one_mul]
  calc
    _ ≤ glyzDecayWeight (A + B) (b • z) *
        ((2 ^ A * glyzDecayWeight A (T x)) * max (1 : ℝ) ‖T (S z)‖ ^ A) :=
      mul_le_mul_of_nonneg_left hs (glyzDecayWeight_pos _ _).le
    _ = (2 ^ A * glyzDecayWeight A (T x)) *
        (max (1 : ℝ) ‖T (S z)‖ ^ A * glyzDecayWeight (A + B) (b • z)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity [glyzDecayWeight_pos A (T x)])

/-- A scale-independent subspace convolution bound. Taking B = n > l
gives the safe v3 choice A' = A+n. -/
theorem integral_glyzDecayWeight_subspace_le {l n B : ℕ} (A : ℕ) (hB : l < B)
    (T : Base n →ₗ[ℝ] Base n) (S : Base l →ₗ[ℝ] Base n)
    {b : ℝ} (hb : 0 < b) (hTS : ∀ z, ‖T (S z)‖ ≤ b * ‖z‖) (x : Base n) :
    (∫ z : Base l, glyzIsotropicWeight (A + B) b z * glyzDecayWeight A (T (x - S z))) ≤
      (2 ^ A * ∫ z : Base l, glyzDecayWeight B z) * glyzDecayWeight A (T x) := by
  have hg := integrable_glyzIsotropicWeight hB hb
  have hdom (z : Base l) :
      glyzIsotropicWeight (A + B) b z * glyzDecayWeight A (T (x - S z)) ≤
        (2 ^ A * glyzDecayWeight A (T x)) * glyzIsotropicWeight B b z := by
    simpa only [glyzIsotropicWeight, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left (glyzDecayWeight_subspace_pointwise A B T S hb hTS x z)
        (pow_pos hb l).le
  have hprod : Integrable (fun z : Base l => glyzIsotropicWeight (A + B) b z *
      glyzDecayWeight A (T (x - S z))) := by
    apply (hg.const_mul (2 ^ A * glyzDecayWeight A (T x))).mono'
      (by
        apply Continuous.aestronglyMeasurable
        unfold glyzIsotropicWeight
        exact (continuous_const.mul ((continuous_glyzDecayWeight (A + B)).comp
          (continuous_const.smul continuous_id))).mul
          ((continuous_glyzDecayWeight A).comp (T.continuous_of_finiteDimensional.comp
            (continuous_const.sub (S.continuous_of_finiteDimensional)))))
    exact Filter.Eventually.of_forall fun z => by
      change |b ^ l * glyzDecayWeight (A + B) (b • z) * glyzDecayWeight A (T (x - S z))| ≤ _
      rw [abs_of_pos (mul_pos (mul_pos (pow_pos hb l)
        (glyzDecayWeight_pos _ _)) (glyzDecayWeight_pos _ _))]
      exact hdom z
  calc
    _ ≤ ∫ z : Base l, (2 ^ A * glyzDecayWeight A (T x)) * glyzIsotropicWeight B b z :=
      integral_mono hprod (hg.const_mul _) hdom
    _ = _ := by rw [integral_const_mul, integral_glyzIsotropicWeight B hb]; ring

def glyzTailInjection (k l : ℕ) : Base l →ₗ[ℝ] Base (k + l) :=
  (mixedJetFlatten k l).toLinearMap.comp (LinearMap.inr ℝ (Base k) (Base l))

theorem norm_glyzMomentDilation_tail_le (k l : ℕ) {ν : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (z : Base l) :
    ‖glyzMomentDilation (k + l) ν hν.ne' (glyzTailInjection k l z)‖ ≤ ν ^ (k + 1) * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change ‖ν ^ ((j : ℕ) + 1) * mixedJetFlatten k l (0, z) (j.castAdd l)‖ ≤ _
    rw [mixedJetFlatten_apply_left]
    simp
    positivity
  · change ‖ν ^ (((j.natAdd k : Fin (k + l)) : ℕ) + 1) *
      mixedJetFlatten k l (0, z) (j.natAdd k)‖ ≤ _
    rw [mixedJetFlatten_apply_right, norm_mul, Real.norm_eq_abs,
      abs_of_pos (pow_pos hν _)]
    exact mul_le_mul
      (pow_le_pow_of_le_one hν.le hν₁ (by simp only [Fin.val_natAdd]; omega))
      (norm_le_pi_norm z j) (norm_nonneg _) (pow_pos hν _).le

/-- Canonical moment transverse-space case of Appendix A.2 with the
safe exponent A' = A+(k+l), for every positive codimension k. -/
theorem integral_glyzMomentWeight_tail_le {k l : ℕ} (hk : 0 < k) (A : ℕ)
    {ν : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1) (x : Base (k + l)) :
    (∫ z : Base l, glyzIsotropicWeight (A + (k + l)) (ν ^ (k + 1)) z *
      glyzMomentWeight A ν hν.ne' (x - glyzTailInjection k l z)) ≤
      (2 ^ A * ∫ z : Base l, glyzDecayWeight (k + l) z) * glyzMomentWeight A ν hν.ne' x := by
  have h := integral_glyzDecayWeight_subspace_le A (show l < k + l by omega)
    (glyzMomentDilation (k + l) ν hν.ne').toLinearMap (glyzTailInjection k l)
    (pow_pos hν (k + 1)) (norm_glyzMomentDilation_tail_le k l hν hν₁) x
  change (∫ z : Base l, glyzIsotropicWeight (A + (k + l)) (ν ^ (k + 1)) z *
    glyzDecayWeight A (glyzMomentDilation (k + l) ν hν.ne' (x - glyzTailInjection k l z))) ≤
    (2 ^ A * ∫ z : Base l, glyzDecayWeight (k + l) z) *
      glyzDecayWeight A (glyzMomentDilation (k + l) ν hν.ne' x) at h
  have hmul := mul_le_mul_of_nonneg_left h (glyzMomentDensity_pos (k + l) hν).le
  unfold glyzMomentWeight
  rw [← integral_const_mul] at hmul
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

end PlanarNikodym
