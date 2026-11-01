import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricInterpolation
import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricSymmetry

/-! The actual optimal-exponent version of GLYZ Lemma 4.1. The
asymmetric exponents below are defined from supported Schwartz families;
the Hölder recursion is proved, rather than supplied as a record field. -/
noncomputable section
open scoped NNReal
namespace PlanarNikodym

def glyzCriticalNNExponent (k : ℕ) : ℝ≥0 :=
  ⟨glyzCriticalExponent k, glyzCriticalExponent_nonneg k⟩

theorem one_le_glyzCriticalNNExponent {k : ℕ} (hk : 0 < k) :
    1 ≤ glyzCriticalNNExponent k := by
  change (1 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- This is `p_k` times the usual asymmetric optimal loss. -/
def glyzCriticalOptimalAsymmetricLoss (k A l : ℕ) (alpha beta : ℝ) : ℝ :=
  glyzOptimalAsymmetricLoss k A (glyzCriticalNNExponent k) (glyzCriticalExponent l) alpha beta

theorem glyz_critical_optimal_holder_recursion (m r A : ℕ) (hr : 0 < r)
    (hA : m + r + 1 < A) (alpha beta : ℝ) :
    glyzCriticalOptimalAsymmetricLoss (m + r + 1) A (m + 1) alpha beta ≤
      (1 / ((r : ℝ) + 1)) *
        glyzCriticalOptimalAsymmetricLoss (m + r + 1) A r beta alpha +
      ((r : ℝ) / ((r : ℝ) + 1)) *
        glyzCriticalOptimalAsymmetricLoss (m + r + 1) A m alpha beta := by
  let θ : ℝ := 1 / ((r : ℝ) + 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    apply (div_lt_one (by positivity : (0 : ℝ) < (r : ℝ) + 1)).mpr
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    linarith
  have hθ' : 1 - θ = (r : ℝ) / ((r : ℝ) + 1) := by
    dsimp [θ]
    field_simp
    ring
  have ha : θ * (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent r) +
      (1 - θ) * glyzCriticalExponent m = glyzCriticalExponent (m + 1) := by
    dsimp [θ, glyzCriticalExponent]
    push_cast
    field_simp
    ring
  have h := glyzOptimalAsymmetricLoss_logconvex hA
    (glyzCriticalNNExponent (m + r + 1))
    (one_le_glyzCriticalNNExponent (by omega))
    (glyzCriticalExponent_nonneg m)
    (sub_nonneg.mpr (glyzCriticalExponent_mono (show r ≤ m + r + 1 by omega)))
    (glyzCriticalExponent_mono (show m ≤ m + r + 1 by omega))
    (sub_le_self _ (glyzCriticalExponent_nonneg r)) hθ hθ1 alpha beta
  change glyzOptimalAsymmetricLoss (m + r + 1) A (glyzCriticalNNExponent (m + r + 1))
      (θ * (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent r) +
        (1 - θ) * glyzCriticalExponent m) alpha beta ≤ _ at h
  rw [ha] at h
  have hs := glyzOptimalAsymmetricLoss_symm (m + r + 1) A
    (glyzCriticalNNExponent (m + r + 1)) (glyzCriticalExponent r) beta alpha
  change glyzOptimalAsymmetricLoss (m + r + 1) A (glyzCriticalNNExponent (m + r + 1))
    (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent r) alpha beta = _ at hs
  rw [hs, hθ'] at h
  exact h

end PlanarNikodym
