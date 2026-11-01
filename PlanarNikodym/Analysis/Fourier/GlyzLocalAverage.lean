import PlanarNikodym.Analysis.Fourier.GlyzPositiveConvolution

/-! Normalized averages on genuine Euclidean balls in a subspace and
the localization identity used before lower-degree decoupling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

def glyzBallMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] (R : ℝ) : Measure H :=
  (volume (closedBall (0 : H) R))⁻¹ • volume.restrict (closedBall 0 R)

theorem isProbabilityMeasure_glyzBallMeasure {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (glyzBallMeasure H R) := by
  constructor
  simp only [glyzBallMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_closedBall_pos volume (0 : H) hR).ne'
    measure_closedBall_lt_top.ne

theorem ae_glyzBallMeasure_norm_le (R : ℝ) :
    ∀ᵐ z : H ∂glyzBallMeasure H R, ‖z‖ ≤ R := by
  apply Measure.ae_smul_measure
  exact (ae_restrict_mem measurableSet_closedBall).mono fun z hz =>
    by simpa only [mem_closedBall, dist_zero_right] using hz

/-- Averaging the product preserves its full-space integral. A local
shift bound for the second factor then removes it from the local average. -/
theorem glyz_localize_bilinear (μ : Measure H) [IsProbabilityMeasure μ]
    (S : H →L[ℝ] E) {F G : E → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hshift : ∀ x, ∀ᵐ z ∂μ, G (x - S z) ≤ C * G x) :
    (∫⁻ x, F x * G x) ≤ C * ∫⁻ x, glyzSubspaceAverage μ S F x * G x := by
  have hmass : (∫⁻ x, glyzSubspaceAverage μ S (fun y => F y * G y) x) =
      ∫⁻ x, F x * G x := by
    rw [glyzSubspaceAverage_mass μ S (hF.mul hG), measure_univ, one_mul]
  rw [← hmass]
  calc
    _ ≤ ∫⁻ x, C * (glyzSubspaceAverage μ S F x * G x) := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ ∫⁻ z, F (x - S z) * (C * G x) ∂μ :=
          lintegral_mono_ae ((hshift x).mono fun z hz => mul_le_mul' le_rfl hz)
        _ = _ := by
          have hf : Measurable (fun z => F (x - S z)) :=
            hF.comp (continuous_const.sub S.continuous).measurable
          rw [lintegral_mul_const _ hf]
          change glyzSubspaceAverage μ S F x * (C * G x) = _
          ring
    _ = _ := lintegral_const_mul' _ _ hC

end PlanarNikodym
