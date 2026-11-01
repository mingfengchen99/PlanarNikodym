import PlanarNikodym.Analysis.Fourier.GlyzWeightedHolder

/-! The actual asymmetric Holder recursion at the critical moment-curve
exponents. This is the integral inequality underlying GLYZ Lemma 4.1. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

def glyzCriticalExponent (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 1)

theorem glyzCriticalExponent_nonneg (m : ℕ) : 0 ≤ glyzCriticalExponent m := by
  unfold glyzCriticalExponent
  positivity

theorem glyzCriticalExponent_mono {m n : ℕ} (h : m ≤ n) :
    glyzCriticalExponent m ≤ glyzCriticalExponent n := by
  unfold glyzCriticalExponent
  have h' : (m : ℝ) ≤ n := by exact_mod_cast h
  nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Write l=m+1 and k=l+r. The two actual convolution-power integrals
on the right have the exponents (p_k-p_r,p_r) and (p_m,p_k-p_m).
The interpolation weights are exactly 1/(r+1) and r/(r+1). -/
theorem glyz_asymmetric_holder_recursion (m r : ℕ) (hr : 0 < r)
    (μ ν : Measure E) [SFinite μ] [SFinite ν] (f g : SchwartzMap E ℂ) :
    glyzWeightedBilinear μ ν f g (glyzCriticalExponent (m + 1))
        (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent (m + 1)) ≤
      glyzWeightedBilinear μ ν f g
          (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent r) (glyzCriticalExponent r) ^
            (1 / ((r : ℝ) + 1)) *
        glyzWeightedBilinear μ ν f g (glyzCriticalExponent m)
          (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent m) ^
            ((r : ℝ) / ((r : ℝ) + 1)) := by
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
  have hb : θ * glyzCriticalExponent r +
      (1 - θ) * (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent m) =
        glyzCriticalExponent (m + r + 1) - glyzCriticalExponent (m + 1) := by
    nlinarith [ha]
  have h := glyzWeightedBilinear_logconvex μ ν f g
    (glyzCriticalExponent_nonneg m)
    (sub_nonneg.mpr (glyzCriticalExponent_mono (show r ≤ m + r + 1 by omega)))
    (sub_nonneg.mpr (glyzCriticalExponent_mono (show m ≤ m + r + 1 by omega)))
    (glyzCriticalExponent_nonneg r) hθ hθ1
  rw [ha, hb, hθ'] at h
  exact h

end PlanarNikodym
