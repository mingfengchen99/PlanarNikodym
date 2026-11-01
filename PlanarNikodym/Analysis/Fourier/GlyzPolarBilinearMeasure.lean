import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricHolder

/-! Finite measures from the actual polar-box weights. Their averages
are the actual convolutions in the asymmetric bilinear integral. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem continuous_glyzPolarWeight {m : ℕ} (A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :
    Continuous (glyzPolarWeight A L) := by
  unfold glyzPolarWeight glyzBoxWeight glyzBoxCoordinates
  exact continuous_const.mul (continuous_const.mul
    ((continuous_glyzDecayWeight A).comp
      ((EuclideanSpace.equiv (Fin m) ℝ).continuous.comp (glyzAdjointEquiv L).continuous)))

def glyzPolarMeasure {m : ℕ} (A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) : Measure (GlyzSpace m) :=
  volume.withDensity (fun y => ENNReal.ofReal (glyzPolarWeight A L y))

theorem isFiniteMeasure_glyzPolarMeasure {m A : ℕ} (hA : m < A)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) : IsFiniteMeasure (glyzPolarMeasure A L) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_glyzPolarWeight hA L)
    (Filter.Eventually.of_forall fun y => (glyzPolarWeight_pos A L y).le)]
  exact ENNReal.ofReal_ne_top

theorem glyzPolarMeasure_average {m : ℕ} (A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (f : SchwartzMap (GlyzSpace m) ℂ) (a : ℝ) (x : GlyzSpace m) :
    glyzPowerAverage (glyzPolarMeasure A L) f a x =
      ∫⁻ y, ‖f (x - y)‖ₑ ^ a * ENNReal.ofReal (glyzPolarWeight A L y) := by
  unfold glyzPowerAverage glyzPolarMeasure
  have hf : Measurable (fun y : GlyzSpace m => ‖f (x - y)‖ₑ ^ a) :=
    (f.continuous.comp (continuous_const.sub continuous_id)).measurable.enorm.pow_const a
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (continuous_glyzPolarWeight A L).measurable.ennreal_ofReal
      hf]
  apply lintegral_congr
  intro y
  exact mul_comm _ _

/-- GLYZ's asymmetric Holder integral recursion with the actual
volume-normalized polar-box weights, for arbitrary two frames. -/
theorem glyz_polar_asymmetric_holder (m r A : ℕ) (hr : 0 < r) (hA : m + r + 1 < A)
    (L₁ L₂ : GlyzSpace (m + r + 1) ≃L[ℝ] GlyzSpace (m + r + 1))
    (f g : SchwartzMap (GlyzSpace (m + r + 1)) ℂ) :
    glyzWeightedBilinear (glyzPolarMeasure A L₁) (glyzPolarMeasure A L₂) f g
        (glyzCriticalExponent (m + 1))
        (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent (m + 1)) ≤
      glyzWeightedBilinear (glyzPolarMeasure A L₁) (glyzPolarMeasure A L₂) f g
          (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent r) (glyzCriticalExponent r) ^
            (1 / ((r : ℝ) + 1)) *
        glyzWeightedBilinear (glyzPolarMeasure A L₁) (glyzPolarMeasure A L₂) f g
          (glyzCriticalExponent m) (glyzCriticalExponent (m + r + 1) - glyzCriticalExponent m) ^
            ((r : ℝ) / ((r : ℝ) + 1)) := by
  letI := isFiniteMeasure_glyzPolarMeasure hA L₁
  letI := isFiniteMeasure_glyzPolarMeasure hA L₂
  exact glyz_asymmetric_holder_recursion m r hr _ _ f g

end PlanarNikodym
