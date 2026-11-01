import PlanarNikodym.Analysis.Fourier.GlyzFourierAffine
import PlanarNikodym.Analysis.Fourier.GlyzReproducingKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! An actual smooth Fourier cutoff on affine frequency ellipsoids.
Its inverse transform has uniform mass and uniform adapted decay. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory FourierTransform
open scoped FourierTransform ENNReal NNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E]

def glyzNormWeight (A : ℕ) (x : E) : ℝ := (max (1 : ℝ) ‖x‖ ^ A)⁻¹

theorem glyzNormWeight_pos (A : ℕ) (x : E) : 0 < glyzNormWeight A x := by
  unfold glyzNormWeight
  positivity

variable [InnerProductSpace ℝ E]

theorem glyz_schwartz_decay_weight (K : SchwartzMap E ℂ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖K x‖ ≤ C * glyzNormWeight A x := by
  obtain ⟨C₀, hC₀, h₀⟩ := K.decay 0 0
  obtain ⟨C₁, hC₁, h₁⟩ := K.decay A 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h₀
  simp only [norm_iteratedFDeriv_zero] at h₁
  refine ⟨max C₀ C₁, lt_of_lt_of_le hC₀ (le_max_left _ _), fun x => ?_⟩
  unfold glyzNormWeight
  by_cases hx : ‖x‖ ≤ 1
  · rw [max_eq_left hx, one_pow, inv_one, mul_one]
    exact (h₀ x).trans (le_max_left _ _)
  · rw [max_eq_right (le_of_not_ge hx)]
    have hp : 0 < ‖x‖ ^ A := pow_pos (lt_of_lt_of_le zero_lt_one (le_of_not_ge hx)) A
    change ‖K x‖ ≤ max C₀ C₁ / ‖x‖ ^ A
    apply (le_div_iff₀ hp).mpr
    nlinarith [h₁ x, le_max_right C₀ C₁]

variable [FiniteDimensional ℝ E]

def glyzBaseBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : E) :=
  ⟨R, R + 1, hR, by linarith⟩

def glyzBaseCutoff (R : ℝ) (hR : 0 < R) : SchwartzMap E ℂ :=
  (((glyzBaseBump R hR : ContDiffBump (0 : E)).hasCompactSupport).comp_left
    (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (glyzBaseBump R hR).contDiff)

theorem glyzBaseCutoff_eq_one (R : ℝ) (hR : 0 < R) {ξ : E} (hξ : ‖ξ‖ ≤ R) :
    glyzBaseCutoff (E := E) R hR ξ = 1 := by
  change ((((glyzBaseBump R hR : ContDiffBump (0 : E)) : E → ℝ) ξ : ℝ) : ℂ) = 1
  rw [(glyzBaseBump R hR).one_of_mem_closedBall (by
    simpa [mem_closedBall, dist_zero_right, glyzBaseBump] using hξ)]
  rfl

def glyzAffineCutoff (L : E ≃L[ℝ] E) (a : E) (R : ℝ) (hR : 0 < R) : SchwartzMap E ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (glyzBaseCutoff R hR)).compSubConstCLM ℂ a

@[simp] theorem glyzAffineCutoff_apply (L : E ≃L[ℝ] E) (a : E) (R : ℝ) (hR : 0 < R) (ξ : E) :
    glyzAffineCutoff L a R hR ξ = glyzBaseCutoff R hR (L.symm (ξ - a)) := rfl

def glyzAffineWeight (A : ℕ) (L : E ≃L[ℝ] E) (x : E) : ℝ :=
  |LinearMap.det L.toLinearMap| * glyzNormWeight A (glyzAdjointEquiv L x)

theorem glyzAffineWeight_pos (A : ℕ) (L : E ≃L[ℝ] E) (x : E) :
    0 < glyzAffineWeight A L x :=
  mul_pos (abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero)
    (glyzNormWeight_pos A _)

variable [MeasurableSpace E] [BorelSpace E]

theorem norm_glyzAffineKernel (L : E ≃L[ℝ] E) (a : E) (R : ℝ) (hR : 0 < R) (x : E) :
    ‖glyzReproducingKernel (glyzAffineCutoff L a R hR) x‖ =
      |LinearMap.det L.toLinearMap| *
        ‖glyzReproducingKernel (glyzBaseCutoff R hR) (glyzAdjointEquiv L x)‖ := by
  have he := congrArg norm (glyz_fourierInv_affine L a (glyzBaseCutoff R hR) x)
  have hf : (glyzAffineCutoff L a R hR : E → ℂ) =
      fun ξ => glyzBaseCutoff R hR (L.symm (ξ - a)) := rfl
  simpa only [glyzReproducingKernel, SchwartzMap.fourierInv_coe, hf,
    norm_mul, Circle.norm_coe, one_mul, norm_smul, Real.norm_eq_abs, abs_abs] using he

/-- The L¹ norm of the actual rescaled reproducing kernel is independent
of every affine frame and frequency center. -/
theorem integral_norm_glyzAffineKernel (L : E ≃L[ℝ] E) (a : E) (R : ℝ) (hR : 0 < R) :
    (∫ x, ‖glyzReproducingKernel (glyzAffineCutoff L a R hR) x‖) =
      ∫ x : E, ‖glyzReproducingKernel (glyzBaseCutoff R hR) x‖ := by
  simp_rw [norm_glyzAffineKernel]
  rw [integral_const_mul, glyz_integral_comp_linearEquiv (glyzAdjointEquiv L)
      (fun y : E => ‖glyzReproducingKernel (glyzBaseCutoff R hR) y‖), smul_eq_mul,
    det_glyzAdjointEquiv, ← mul_assoc, ← abs_mul,
    mul_inv_cancel₀ (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero, abs_one, one_mul]

theorem glyzAffineKernel_uniform_decay (R : ℝ) (hR : 0 < R) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : E ≃L[ℝ] E) (a x : E),
      ‖glyzReproducingKernel (glyzAffineCutoff L a R hR) x‖ ≤ C * glyzAffineWeight A L x := by
  obtain ⟨C, hC, hdec⟩ := glyz_schwartz_decay_weight
    (glyzReproducingKernel (glyzBaseCutoff (E := E) R hR)) A
  refine ⟨C, hC, fun L a x => ?_⟩
  rw [norm_glyzAffineKernel]
  simpa only [glyzAffineWeight, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hdec (glyzAdjointEquiv L x))
      (abs_nonneg (LinearMap.det L.toLinearMap))

end PlanarNikodym
