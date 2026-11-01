import PlanarNikodym.Analysis.Fourier.GlyzAffineCutoff

/-! The actual pointwise uncertainty estimate with one constant uniform
over all invertible frequency frames and all frequency centers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform
open scoped FourierTransform ENNReal NNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_enorm_glyzAffineKernel (L : E ≃L[ℝ] E) (a : E) (R : ℝ) (hR : 0 < R) :
    (∫⁻ x, ‖glyzReproducingKernel (glyzAffineCutoff L a R hR) x‖ₑ) =
      ∫⁻ x : E, ‖glyzReproducingKernel (glyzBaseCutoff R hR) x‖ₑ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    (glyzReproducingKernel (glyzAffineCutoff L a R hR)).integrable,
    ← ofReal_integral_norm_eq_lintegral_enorm
    (glyzReproducingKernel (glyzBaseCutoff (E := E) R hR)).integrable,
    integral_norm_glyzAffineKernel]

/-- GLYZ Lemma 3.3 for affine frequency balls. The actual Schwartz
reproducing kernel, its decay and its scale-independent mass are all
constructed in the proof; the only input hypothesis is Fourier support. -/
theorem glyz_uncertainty_affine_ball (A : ℕ) (R : ℝ) (hR : 0 < R)
    {p : ℝ≥0} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : E ≃L[ℝ] E) (a : E) (f : SchwartzMap E ℂ),
      Function.support (𝓕 (f : E → ℂ)) ⊆ {ξ | ‖L.symm (ξ - a)‖ ≤ R} →
      ∀ x, ‖f x‖ₑ ^ (p : ℝ) ≤ ENNReal.ofReal C *
        ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzAffineWeight A L y) := by
  obtain ⟨B, hB, hdec⟩ := glyzAffineKernel_uniform_decay (E := E) R hR A
  let M : ℝ≥0∞ := ∫⁻ y : E, ‖glyzReproducingKernel (glyzBaseCutoff R hR) y‖ₑ
  have hM : M ≠ ∞ := (glyzReproducingKernel (glyzBaseCutoff (E := E) R hR)).integrable.hasFiniteIntegral.ne
  have hp1 : 0 ≤ (p : ℝ) - 1 := by
    have h : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  let D : ℝ≥0∞ := ENNReal.ofReal B * M ^ ((p : ℝ) - 1)
  have hD : D ≠ ∞ := by dsimp [D]; finiteness
  have hC : 0 < D.toReal + 1 := by positivity
  have hDC : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨D.toReal + 1, hC, fun L a f hs x => ?_⟩
  have hχ : ∀ ξ ∈ Function.support (𝓕 (f : E → ℂ)), glyzAffineCutoff L a R hR ξ = 1 := by
    intro ξ hξ
    exact glyzBaseCutoff_eq_one R hR (hs hξ)
  have hh := glyz_pointwise_reproducing_holder f (glyzAffineCutoff L a R hR) hχ hp x
  rw [lintegral_enorm_glyzAffineKernel] at hh
  have hbound (y : E) : ‖glyzReproducingKernel (glyzAffineCutoff L a R hR) y‖ₑ ≤
      ENNReal.ofReal B * ENNReal.ofReal (glyzAffineWeight A L y) := by
    have h := ENNReal.ofReal_le_ofReal (hdec L a y)
    simpa only [ofReal_norm, ENNReal.ofReal_mul hB.le] using h
  calc
    _ ≤ (∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
        ‖glyzReproducingKernel (glyzAffineCutoff L a R hR) y‖ₑ) * M ^ ((p : ℝ) - 1) := hh
    _ ≤ (∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
        (ENNReal.ofReal B * ENNReal.ofReal (glyzAffineWeight A L y))) * M ^ ((p : ℝ) - 1) :=
      mul_le_mul_left (lintegral_mono (fun y => mul_le_mul_right (hbound y) _)) _
    _ = D * ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzAffineWeight A L y) := by
      have he : (∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
          (ENNReal.ofReal B * ENNReal.ofReal (glyzAffineWeight A L y))) =
          ENNReal.ofReal B * ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzAffineWeight A L y) := by
        calc
          _ = ∫⁻ y, ENNReal.ofReal B * (‖f (x - y)‖ₑ ^ (p : ℝ) *
              ENNReal.ofReal (glyzAffineWeight A L y)) := by
            apply lintegral_congr
            intro y
            ring
          _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      rw [he]
      dsimp [D]
      ring
    _ ≤ _ := mul_le_mul_left hDC _

end PlanarNikodym
