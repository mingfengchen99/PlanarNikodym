import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricLinearBound
import PlanarNikodym.Analysis.Fourier.GlyzOptimalHolderRecursion
import PlanarNikodym.Analysis.Fourier.GlyzSignedLiminfBootstrap

/-! Signed deviations of the genuine optimal asymmetric exponents.
The linear exponent is measured for squared constants, and the asymmetric
exponent is multiplied by `2 / p_k` to use the same normalization.
Index zero is the constant linear loss; it is a boundary value used in the
finite bootstrap, not an assertion about a nonexistent separated depth-zero
asymmetric family. -/
noncomputable section
open Filter Topology
open scoped NNReal
namespace PlanarNikodym

def glyzCriticalScaleRatio (k l : ℕ) : ℝ := ((k - l : ℕ) + 1 : ℝ) / (l : ℝ)

def glyzNormalizedCriticalAsymmetricLoss (k A l : ℕ) (alpha beta : ℝ) : ℝ :=
  (2 / glyzCriticalExponent k) * glyzCriticalOptimalAsymmetricLoss k A l alpha beta

/-- A real signed quantity. No nonnegative truncation occurs here. -/
def glyzCriticalSignedDeviation (k A l : ℕ) (b : ℝ) : ℝ :=
  if l = 0 then glyzOptimalSquareLoss k (glyzCriticalNNExponent k)
  else (glyzOptimalSquareLoss k (glyzCriticalNNExponent k) -
    glyzNormalizedCriticalAsymmetricLoss k A l (glyzCriticalScaleRatio k l * b) b) / b

@[simp] theorem glyzCriticalSignedDeviation_zero (k A : ℕ) (b : ℝ) :
    glyzCriticalSignedDeviation k A 0 b =
      glyzOptimalSquareLoss k (glyzCriticalNNExponent k) := by
  simp [glyzCriticalSignedDeviation]

theorem glyzCriticalScaleRatio_pos {k l : ℕ} (hl : 0 < l) :
    0 < glyzCriticalScaleRatio k l := by
  unfold glyzCriticalScaleRatio
  positivity

theorem glyzCriticalExponent_pos {k : ℕ} (hk : 0 < k) :
    0 < glyzCriticalExponent k := by
  unfold glyzCriticalExponent
  positivity

/-- The true asymmetric exponent is bounded by the true linear exponent
when both relative depths lie in the unit interval. -/
theorem glyzNormalizedCriticalAsymmetricLoss_le_linear {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : l ≤ k) {alpha beta : ℝ}
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hb : 0 ≤ beta) (hb1 : beta ≤ 1) :
    glyzNormalizedCriticalAsymmetricLoss k A l alpha beta ≤
      glyzOptimalSquareLoss k (glyzCriticalNNExponent k) := by
  have hp := glyzCriticalExponent_pos hk
  have he := glyzOptimalSquareLoss_nonneg k (glyzCriticalNNExponent k)
    (one_le_glyzCriticalNNExponent hk)
  have hh := glyzOptimalAsymmetricLoss_le_linear hA (glyzCriticalNNExponent k)
    (one_le_glyzCriticalNNExponent hk) (glyzCriticalExponent_nonneg l)
    (glyzCriticalExponent_mono hl) ha1 hb1
  have hfac : glyzAsymmetricLinearLossFactor (glyzCriticalNNExponent k)
      (glyzCriticalExponent l) alpha beta ≤ glyzCriticalExponent k / 2 := by
    change (1 - alpha) * (glyzCriticalExponent l / 2) +
      (1 - beta) * ((glyzCriticalExponent k - glyzCriticalExponent l) / 2) ≤ _
    nlinarith [mul_nonneg ha (glyzCriticalExponent_nonneg l),
      mul_nonneg hb (sub_nonneg.mpr (glyzCriticalExponent_mono hl))]
  have hnorm := mul_le_mul_of_nonneg_left
    (hh.trans (mul_le_mul_of_nonneg_left hfac he))
    (show 0 ≤ 2 / glyzCriticalExponent k by positivity)
  have heq : (2 / glyzCriticalExponent k) *
      (glyzOptimalSquareLoss k (glyzCriticalNNExponent k) *
        (glyzCriticalExponent k / 2)) =
      glyzOptimalSquareLoss k (glyzCriticalNNExponent k) := by
    field_simp
  exact hnorm.trans_eq heq

/-- The boundary power `a=0` only needs the upper linear comparison.
No sharp endpoint equality or separated depth-zero family is assumed. -/
theorem glyzNormalizedCriticalAsymmetricLoss_zero_le {k A : ℕ}
    (hk : 0 < k) (hA : k < A) {alpha beta : ℝ}
    (ha1 : alpha ≤ 1) (hb1 : beta ≤ 1) :
    glyzNormalizedCriticalAsymmetricLoss k A 0 alpha beta ≤
      (1 - beta) * glyzOptimalSquareLoss k (glyzCriticalNNExponent k) := by
  have hp := glyzCriticalExponent_pos hk
  have hh := glyzOptimalAsymmetricLoss_le_linear hA (glyzCriticalNNExponent k)
    (one_le_glyzCriticalNNExponent hk) (glyzCriticalExponent_nonneg 0)
    (glyzCriticalExponent_mono (Nat.zero_le k)) ha1 hb1
  have hnorm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 2 / glyzCriticalExponent k by positivity)
  apply hnorm.trans_eq
  change (2 / glyzCriticalExponent k) *
    (glyzOptimalSquareLoss k (glyzCriticalNNExponent k) *
      ((1 - alpha) * (glyzCriticalExponent 0 / 2) +
       (1 - beta) * ((glyzCriticalExponent k - glyzCriticalExponent 0) / 2))) = _
  have hz : glyzCriticalExponent 0 = 0 := by norm_num [glyzCriticalExponent]
  rw [hz]
  simp only [zero_div, mul_zero, sub_zero, zero_add]
  field_simp

/-- Restriction to sufficiently small positive scales makes every fixed
rescaling lie in the unit interval. -/
theorem glyz_eventually_scaled_unit (c : ℝ) :
    ∀ᶠ b in 𝓝[>] (0 : ℝ), 0 < b ∧ b ≤ 1 ∧ c * b ≤ 1 := by
  have hb : ∀ᶠ b in 𝓝[>] (0 : ℝ), b < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hcb : ∀ᶠ b in 𝓝[>] (0 : ℝ), c * b < 1 := by
    have ht : Tendsto (fun b : ℝ => c * b) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have ht' := ((continuous_const : Continuous (fun _ : ℝ => c)).mul
        continuous_id).tendsto (0 : ℝ)
      change Tendsto (fun b : ℝ => c * b) (𝓝 (0 : ℝ)) (𝓝 (c * 0)) at ht'
      simpa only [mul_zero] using ht'
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hb, hcb] with b hpos hb hcb
  exact ⟨hpos, hb.le, hcb.le⟩

/-- A genuine lower bound, uniform as the scale tends to zero. -/
theorem glyzCriticalSignedDeviation_eventually_nonneg {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : l ≤ k) :
    ∀ᶠ b in 𝓝[>] (0 : ℝ), 0 ≤ glyzCriticalSignedDeviation k A l b := by
  by_cases hz : l = 0
  · subst l
    exact Eventually.of_forall fun b => by
      simpa using glyzOptimalSquareLoss_nonneg k (glyzCriticalNNExponent k)
        (one_le_glyzCriticalNNExponent hk)
  filter_upwards [glyz_eventually_scaled_unit (glyzCriticalScaleRatio k l)]
    with b hb
  rw [glyzCriticalSignedDeviation, if_neg hz]
  exact div_nonneg (sub_nonneg.mpr (glyzNormalizedCriticalAsymmetricLoss_le_linear
    hk hA hl (mul_nonneg (glyzCriticalScaleRatio_pos (Nat.pos_of_ne_zero hz)).le hb.1.le)
    hb.2.2 hb.1.le hb.2.1)) hb.1.le

theorem glyzCriticalSignedDeviation_boundedBelow {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : l ≤ k) :
    (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·) (glyzCriticalSignedDeviation k A l) :=
  ⟨0, glyzCriticalSignedDeviation_eventually_nonneg hk hA hl⟩

/-- The identity used to pass from a genuine optimal exponent to its signed deviation. -/
theorem glyzNormalizedCriticalAsymmetricLoss_eq_signed {k A l : ℕ}
    (hl : 0 < l) {b : ℝ} (hb : b ≠ 0) :
    glyzNormalizedCriticalAsymmetricLoss k A l (glyzCriticalScaleRatio k l * b) b =
      glyzOptimalSquareLoss k (glyzCriticalNNExponent k) -
        b * glyzCriticalSignedDeviation k A l b := by
  rw [glyzCriticalSignedDeviation, if_neg (Nat.ne_of_gt hl)]
  field_simp
  ring

theorem glyzNormalizedCriticalAsymmetricLoss_holder {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : 0 < l) (hlk : l < k) (alpha beta : ℝ) :
    glyzNormalizedCriticalAsymmetricLoss k A l alpha beta ≤
      (1 / ((k - l : ℕ) + 1 : ℝ)) *
        glyzNormalizedCriticalAsymmetricLoss k A (k - l) beta alpha +
      ((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1 : ℝ) *
        glyzNormalizedCriticalAsymmetricLoss k A (l - 1) alpha beta := by
  have hkform : l - 1 + (k - l) + 1 = k := by omega
  have hlform : l - 1 + 1 = l := by omega
  have hh := glyz_critical_optimal_holder_recursion (l - 1) (k - l) A
    (by omega) (by omega) alpha beta
  rw [hkform, hlform] at hh
  have hh' := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 2 / glyzCriticalExponent k from (div_pos (by norm_num)
      (glyzCriticalExponent_pos hk)).le)
  unfold glyzNormalizedCriticalAsymmetricLoss
  exact hh'.trans_eq (by ring)

/-- The pointwise signed recursion. The two gain inequalities are stated
for the actual optimal exponents, so its eventual version can use GL5 directly. -/
theorem glyzCriticalSignedDeviation_recursion_of_gains {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : 0 < l) (hlk : l < k)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hc1 : glyzCriticalScaleRatio k l * b ≤ 1)
    (hfirst : glyzCriticalOptimalAsymmetricLoss k A (k - l)
        b (glyzCriticalScaleRatio k l * b) ≤
      glyzCriticalOptimalAsymmetricLoss k A (k - l)
        (glyzCriticalScaleRatio k (k - l) * (glyzCriticalScaleRatio k l * b))
        (glyzCriticalScaleRatio k l * b))
    (hprev : 1 < l → glyzCriticalOptimalAsymmetricLoss k A (l - 1)
        (glyzCriticalScaleRatio k l * b) b ≤
      glyzCriticalOptimalAsymmetricLoss k A (l - 1)
        (glyzCriticalScaleRatio k (l - 1) * b) b) :
    glyzCriticalSignedDeviation k A (k - l) (glyzCriticalScaleRatio k l * b) /
        (l : ℝ) +
      ((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1 : ℝ) *
        glyzCriticalSignedDeviation k A (l - 1) b ≤
      glyzCriticalSignedDeviation k A l b := by
  let η := glyzOptimalSquareLoss k (glyzCriticalNNExponent k)
  have hr : 0 < k - l := by omega
  have hn : 0 ≤ 2 / glyzCriticalExponent k := by
    exact (div_pos (by norm_num) (glyzCriticalExponent_pos hk)).le
  have hcb : 0 < glyzCriticalScaleRatio k l * b :=
    mul_pos (glyzCriticalScaleRatio_pos hl) hb
  have hfirst' : glyzNormalizedCriticalAsymmetricLoss k A (k - l)
      b (glyzCriticalScaleRatio k l * b) ≤
      η - (glyzCriticalScaleRatio k l * b) *
        glyzCriticalSignedDeviation k A (k - l) (glyzCriticalScaleRatio k l * b) := by
    have hh := mul_le_mul_of_nonneg_left hfirst hn
    change glyzNormalizedCriticalAsymmetricLoss k A (k - l) _ _ ≤
      glyzNormalizedCriticalAsymmetricLoss k A (k - l) _ _ at hh
    rw [glyzNormalizedCriticalAsymmetricLoss_eq_signed hr hcb.ne'] at hh
    exact hh
  have hprev' : glyzNormalizedCriticalAsymmetricLoss k A (l - 1)
      (glyzCriticalScaleRatio k l * b) b ≤
      η - b * glyzCriticalSignedDeviation k A (l - 1) b := by
    by_cases hl1 : l = 1
    · subst l
      simpa only [Nat.sub_self, glyzCriticalSignedDeviation_zero, η,
        sub_mul, one_mul] using
        glyzNormalizedCriticalAsymmetricLoss_zero_le hk hA hc1 hb1
    · have hh := mul_le_mul_of_nonneg_left (hprev (by omega)) hn
      change glyzNormalizedCriticalAsymmetricLoss k A (l - 1) _ _ ≤
        glyzNormalizedCriticalAsymmetricLoss k A (l - 1) _ _ at hh
      rw [glyzNormalizedCriticalAsymmetricLoss_eq_signed (by omega) hb.ne'] at hh
      exact hh
  have hcomb := (glyzNormalizedCriticalAsymmetricLoss_holder hk hA hl hlk
    (glyzCriticalScaleRatio k l * b) b).trans
    (add_le_add
      (mul_le_mul_of_nonneg_left hfirst' (by positivity))
      (mul_le_mul_of_nonneg_left hprev' (by positivity)))
  rw [glyzNormalizedCriticalAsymmetricLoss_eq_signed hl hb.ne'] at hcomb
  have heq : (1 / ((k - l : ℕ) + 1 : ℝ)) *
      (η - (glyzCriticalScaleRatio k l * b) *
        glyzCriticalSignedDeviation k A (k - l) (glyzCriticalScaleRatio k l * b)) +
      ((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1 : ℝ) *
        (η - b * glyzCriticalSignedDeviation k A (l - 1) b) =
      η - b * (glyzCriticalSignedDeviation k A (k - l)
        (glyzCriticalScaleRatio k l * b) / (l : ℝ) +
        ((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1 : ℝ) *
          glyzCriticalSignedDeviation k A (l - 1) b) := by
    unfold glyzCriticalScaleRatio
    have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
    field_simp
    ring
  rw [heq] at hcomb
  dsimp [η] at hcomb
  nlinarith

theorem glyzCriticalScaleRatio_product_ge_one {k l : ℕ}
    (hl : 0 < l) (hlk : l < k) :
    1 ≤ glyzCriticalScaleRatio k (k - l) * glyzCriticalScaleRatio k l := by
  have hr : 0 < k - l := by omega
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hr' : (0 : ℝ) < (k - l : ℕ) := by exact_mod_cast hr
  have hkr : k - (k - l) = l := by omega
  unfold glyzCriticalScaleRatio
  rw [hkr, div_mul_div_comm]
  apply (le_div_iff₀ (mul_pos hr' hl')).mpr
  nlinarith

theorem glyzCriticalScaleRatio_le_pred {k l : ℕ}
    (hl : 1 < l) (hlk : l ≤ k) :
    glyzCriticalScaleRatio k l ≤ glyzCriticalScaleRatio k (l - 1) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hlp' : (0 : ℝ) < (l - 1 : ℕ) := by exact_mod_cast (show 0 < l - 1 by omega)
  have hkp : k - (l - 1) = k - l + 1 := by omega
  have hlp : ((l - 1 : ℕ) : ℝ) + 1 = l := by exact_mod_cast (show l - 1 + 1 = l by omega)
  unfold glyzCriticalScaleRatio
  rw [hkp]
  push_cast
  apply (div_le_div_iff₀ hl' hlp').mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) (k - l)]

/-- Only finite-dimensional gain inequalities for genuine constants are used
here. Their admissible scales hold eventually, before any lower limit is taken. -/
theorem glyzCriticalSignedDeviation_eventual_recursion {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : 0 < l) (hlk : l < k)
    (hgain : ∀ (j : ℕ), 0 < j → j < k → ∀ (alpha beta : ℝ),
      0 ≤ alpha → alpha ≤ glyzCriticalScaleRatio k j * beta →
      0 < beta → beta ≤ 1 → glyzCriticalScaleRatio k j * beta ≤ 1 →
      glyzCriticalOptimalAsymmetricLoss k A j alpha beta ≤
        glyzCriticalOptimalAsymmetricLoss k A j
          (glyzCriticalScaleRatio k j * beta) beta) :
    ∀ᶠ b in 𝓝[>] (0 : ℝ),
      glyzCriticalSignedDeviation k A (k - l) (glyzCriticalScaleRatio k l * b) /
          (l : ℝ) +
        ((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1 : ℝ) *
          glyzCriticalSignedDeviation k A (l - 1) b ≤
        glyzCriticalSignedDeviation k A l b := by
  filter_upwards [glyz_eventually_scaled_unit (glyzCriticalScaleRatio k l),
    glyz_eventually_scaled_unit (glyzCriticalScaleRatio k (k - l) *
      glyzCriticalScaleRatio k l),
    glyz_eventually_scaled_unit (glyzCriticalScaleRatio k (l - 1))] with b hb hbr hbp
  apply glyzCriticalSignedDeviation_recursion_of_gains hk hA hl hlk hb.1 hb.2.1 hb.2.2
  · apply hgain (k - l) (by omega) (by omega) b
      (glyzCriticalScaleRatio k l * b) hb.1.le
    · have hh := mul_le_mul_of_nonneg_right
        (glyzCriticalScaleRatio_product_ge_one hl hlk) hb.1.le
      simpa only [one_mul, mul_assoc] using hh
    · exact mul_pos (glyzCriticalScaleRatio_pos hl) hb.1
    · exact hb.2.2
    · simpa only [mul_assoc] using hbr.2.2
  · intro hl1
    apply hgain (l - 1) (by omega) (by omega)
      (glyzCriticalScaleRatio k l * b) b
      (mul_nonneg (glyzCriticalScaleRatio_pos hl).le hb.1.le)
      (mul_le_mul_of_nonneg_right (glyzCriticalScaleRatio_le_pred hl1 hlk.le) hb.1.le)
      hb.1 hb.2.1 hbp.2.2

end PlanarNikodym
