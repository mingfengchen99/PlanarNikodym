import PlanarNikodym.Analysis.Fourier.GlyzCriticalSignedDeviation
import PlanarNikodym.Analysis.Fourier.GlyzLinearReverseLoss

/-! The finite, real lower-limit bootstrap for the actual optimal constants.
Whitney's reverse comparison supplies the missing upper bound on signed
deviations; the linear comparison supplies the lower bound. The remaining
analytic premise in the final lemma is stated explicitly as a scale-gain
inequality for the genuine optimal asymmetric constants. -/
noncomputable section
open Filter Topology
open scoped NNReal
namespace PlanarNikodym

def glyzCriticalDeviationUpperBound (k l : ℕ) : ℝ :=
  (2 / glyzCriticalExponent k) * (glyzCriticalExponent l * glyzCriticalScaleRatio k l +
    (glyzCriticalExponent k - glyzCriticalExponent l))

theorem two_le_glyzCriticalNNExponent {k : ℕ} (hk : 0 < k) :
    2 ≤ glyzCriticalNNExponent k := by
  change (2 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Whitney's actual reverse bound makes the signed deviation finite above. -/
theorem glyzCriticalSignedDeviation_eventually_le {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : 0 < l) (hlk : l < k) :
    ∀ᶠ b in 𝓝[>] (0 : ℝ), glyzCriticalSignedDeviation k A l b ≤
      glyzCriticalDeviationUpperBound k l := by
  have ha : 1 ≤ glyzCriticalExponent l :=
    (show (1 : ℝ) ≤ (glyzCriticalNNExponent l : ℝ) from
      one_le_glyzCriticalNNExponent hl)
  have hb : 1 ≤ glyzCriticalExponent k - glyzCriticalExponent l := by
    have hl' : (0 : ℝ) ≤ l := by positivity
    have hkl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hlk
    unfold glyzCriticalExponent
    nlinarith
  filter_upwards [glyz_eventually_scaled_unit (glyzCriticalScaleRatio k l)] with b hb'
  have hh := glyzOptimalSquareLoss_le_asymmetric hA (glyzCriticalNNExponent k)
    (two_le_glyzCriticalNNExponent hk) ha hb
    (mul_pos (glyzCriticalScaleRatio_pos hl) hb'.1) hb'.1 hb'.2.2 hb'.2.1
  change glyzOptimalSquareLoss k (glyzCriticalNNExponent k) ≤
    (2 / glyzCriticalExponent k) * (glyzCriticalExponent l *
      (glyzCriticalScaleRatio k l * b) + (glyzCriticalExponent k - glyzCriticalExponent l) * b +
      glyzCriticalOptimalAsymmetricLoss k A l (glyzCriticalScaleRatio k l * b) b) at hh
  have heq : (2 / glyzCriticalExponent k) * (glyzCriticalExponent l *
      (glyzCriticalScaleRatio k l * b) + (glyzCriticalExponent k - glyzCriticalExponent l) * b +
      glyzCriticalOptimalAsymmetricLoss k A l (glyzCriticalScaleRatio k l * b) b) =
      glyzCriticalDeviationUpperBound k l * b +
        glyzNormalizedCriticalAsymmetricLoss k A l (glyzCriticalScaleRatio k l * b) b := by
    unfold glyzCriticalDeviationUpperBound glyzNormalizedCriticalAsymmetricLoss
    ring
  rw [heq] at hh
  rw [glyzCriticalSignedDeviation, if_neg hl.ne']
  exact (div_le_iff₀ hb'.1).mpr (by linarith)

theorem glyzCriticalSignedDeviation_boundedAbove {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hlk : l < k) :
    (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) (glyzCriticalSignedDeviation k A l) := by
  by_cases hl : l = 0
  · subst l
    refine ⟨glyzOptimalSquareLoss k (glyzCriticalNNExponent k), ?_⟩
    change ∀ᶠ b in 𝓝[>] (0 : ℝ), glyzCriticalSignedDeviation k A 0 b ≤
      glyzOptimalSquareLoss k (glyzCriticalNNExponent k)
    exact Eventually.of_forall fun b => by simp
  · exact ⟨glyzCriticalDeviationUpperBound k l,
      glyzCriticalSignedDeviation_eventually_le hk hA (Nat.pos_of_ne_zero hl) hlk⟩

/-- This lower limit is finite in the critical range, as shown by the two
actual-constant bounds. In particular it is not the infimum of nonnegative
admissible exponents appearing in the definition of the original constants. -/
def glyzCriticalSignedLiminf (k A l : ℕ) : ℝ :=
  liminf (glyzCriticalSignedDeviation k A l) (𝓝[>] (0 : ℝ))

@[simp] theorem glyzCriticalSignedLiminf_zero (k A : ℕ) :
    glyzCriticalSignedLiminf k A 0 = glyzOptimalSquareLoss k (glyzCriticalNNExponent k) := by
  unfold glyzCriticalSignedLiminf
  have heq : glyzCriticalSignedDeviation k A 0 =
      fun _ => glyzOptimalSquareLoss k (glyzCriticalNNExponent k) :=
    funext (fun b => glyzCriticalSignedDeviation_zero k A b)
  rw [heq, liminf_const]

theorem glyzCriticalSignedLiminf_nonneg {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hlk : l < k) :
    0 ≤ glyzCriticalSignedLiminf k A l :=
  le_liminf_of_le (glyzCriticalSignedDeviation_boundedAbove hk hA hlk).isCoboundedUnder_ge
    (glyzCriticalSignedDeviation_eventually_nonneg hk hA hlk.le)

theorem glyzCriticalSignedLiminf_le {k A l : ℕ}
    (hk : 0 < k) (hA : k < A) (hl : 0 < l) (hlk : l < k) :
    glyzCriticalSignedLiminf k A l ≤ glyzCriticalDeviationUpperBound k l := by
  have hh := liminf_le_liminf (glyzCriticalSignedDeviation_eventually_le hk hA hl hlk)
    (glyzCriticalSignedDeviation_boundedBelow hk hA hlk.le)
    (show (𝓝[>] (0 : ℝ)).IsCoboundedUnder (· ≥ ·)
      (fun _ => glyzCriticalDeviationUpperBound k l) from
      (show (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
        (fun _ => glyzCriticalDeviationUpperBound k l) from
        isBoundedUnder_const).isCoboundedUnder_ge)
  unfold glyzCriticalSignedLiminf
  rw [liminf_const] at hh
  exact hh

/-- Once the genuine lower-dimensional scale gain is supplied, the actual
critical linear exponent vanishes. No limiting exponent or its finiteness is
postulated: they are obtained from actual constants and Whitney's inequality. -/
theorem glyz_critical_optimal_zero_of_gain {k A : ℕ}
    (hk : 1 < k) (hA : k < A)
    (hgain : ∀ (j : ℕ), 0 < j → j < k → ∀ (alpha beta : ℝ),
      0 ≤ alpha → alpha ≤ glyzCriticalScaleRatio k j * beta →
      0 < beta → beta ≤ 1 → glyzCriticalScaleRatio k j * beta ≤ 1 →
      glyzCriticalOptimalAsymmetricLoss k A j alpha beta ≤
        glyzCriticalOptimalAsymmetricLoss k A j
          (glyzCriticalScaleRatio k j * beta) beta) :
    glyzOptimalSquareLoss k (glyzCriticalNNExponent k) = 0 := by
  have hk0 : 0 < k := by omega
  apply glyz_signed_functional_bootstrap_zero (N := k - 1) (by omega)
    (glyzCriticalSignedDeviation k A) (fun i => glyzCriticalScaleRatio k (i + 1))
    (glyzOptimalSquareLoss_nonneg k (glyzCriticalNNExponent k)
      (one_le_glyzCriticalNNExponent hk0))
  · exact Eventually.of_forall fun b => glyzCriticalSignedDeviation_zero k A b
  · intro i hi
    exact glyzCriticalSignedDeviation_boundedBelow hk0 hA (by omega)
  · intro i hi
    exact glyzCriticalSignedDeviation_boundedAbove hk0 hA (by omega)
  · intro i hi
    exact glyzCriticalScaleRatio_pos (by omega)
  · intro i hi
    have hh := glyzCriticalSignedDeviation_eventual_recursion hk0 hA
      (show 0 < i + 1 by omega) (show i + 1 < k by omega) hgain
    have hsub : k - (i + 1) = k - 1 - i := by omega
    simpa only [hsub, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using hh

end PlanarNikodym
