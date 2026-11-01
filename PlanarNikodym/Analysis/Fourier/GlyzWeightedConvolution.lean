import PlanarNikodym.Analysis.Fourier.GlyzTransverseWeight

/-! Propagation of the actual subspace weight estimate to the
convolved Schwartz power appearing in the asymmetric bilinear integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

def glyzPositiveConvolution (F w : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ∫⁻ y, F y * w (x - y)

theorem measurable_glyzPositiveConvolution {F w : E → ℝ≥0∞}
    (hF : Measurable F) (hw : Measurable w) : Measurable (glyzPositiveConvolution F w) :=
  Measurable.lintegral_prod_right ((hF.comp measurable_snd).mul
    (hw.comp (continuous_fst.sub continuous_snd).measurable))

theorem glyzPositiveConvolution_comm {F w : E → ℝ≥0∞} (x : E) :
    glyzPositiveConvolution F w x = ∫⁻ y, F (x - y) * w y := by
  symm
  simpa only [sub_sub_cancel, glyzPositiveConvolution] using
    (lintegral_sub_left_eq_self (fun y => F y * w (x - y)) x)

omit [FiniteDimensional ℝ H] in
/-- A subspace convolution bound for the kernel propagates to its
convolution with any measurable nonnegative function. -/
theorem glyzPositiveConvolution_subspace_stable (μ : Measure H) [SFinite μ]
    (S : H →L[ℝ] E) {F w : E → ℝ≥0∞} (hF : Measurable F) (hw : Measurable w)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hstable : ∀ x, glyzSubspaceAverage μ S w x ≤ C * w x)
    (x : E) :
    glyzSubspaceAverage μ S (glyzPositiveConvolution F w) x ≤
      C * glyzPositiveConvolution F w x := by
  unfold glyzSubspaceAverage glyzPositiveConvolution
  have hm : Measurable (fun z : H × E => F z.2 * w (x - S z.1 - z.2)) :=
    (hF.comp measurable_snd).mul (hw.comp
      ((continuous_const.sub (S.continuous.comp continuous_fst)).sub continuous_snd).measurable)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have he (y : E) :
      (∫⁻ z : H, F y * w (x - S z - y) ∂μ) = F y * glyzSubspaceAverage μ S w (x - y) := by
    have he' (z : H) : x - S z - y = x - y - S z := by abel
    simp_rw [he']
    exact lintegral_const_mul _ (hw.comp (continuous_const.sub S.continuous).measurable)
  simp_rw [he]
  calc
    _ ≤ ∫⁻ y, C * (F y * w (x - y)) := lintegral_mono fun y =>
      (mul_le_mul' le_rfl (hstable (x - y))).trans_eq (by ring)
    _ = _ := lintegral_const_mul' _ _ hC

theorem glyzPolarMeasure_powerAverage_eq_convolution {m : ℕ} (A : ℕ)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (f : SchwartzMap (GlyzSpace m) ℂ) (a : ℝ) (x : GlyzSpace m) :
    glyzPowerAverage (glyzPolarMeasure A L) f a x =
      glyzPositiveConvolution (fun y => ‖f y‖ₑ ^ a) (fun y => ENNReal.ofReal (glyzPolarWeight A L y)) x := by
  rw [glyzPolarMeasure_average, glyzPositiveConvolution_comm]

/-- Uniform Appendix A.2 absorption for the complete second factor in
Lemma 3.8, with every Schwartz function and every real power. -/
theorem exists_uniform_glyz_transverse_powerAverage (l r A : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ δ : ℝ, ∀ hδ : 0 < δ,
      δ ≤ 1 → ∀ (g : SchwartzMap (GlyzSpace (l + r)) ℂ) (q : ℝ) (x : GlyzSpace (l + r)),
      glyzSubspaceAverage
        (glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t) (A + (l + r)) (δ ^ (r + 1)))
        (glyzEuclideanTangentSpace (l + r) r t)ᗮ.subtypeL
        (glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q) x ≤
      ENNReal.ofReal C *
        glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q x := by
  obtain ⟨C, hC, hweight⟩ := exists_uniform_glyz_transverse_weight l r A hr
  refine ⟨C, hC, ?_⟩
  intro t ht δ hδ hδ1 g q x
  letI := isFiniteMeasure_glyzCoordinateMeasure (glyzOrthogonalCoordinates l r t)
    (show l < A + (l + r) by omega) (pow_pos hδ (r + 1))
  rw [show glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame (l + r) t δ hδ)) g q =
      glyzPositiveConvolution (fun y => ‖g y‖ₑ ^ q)
        (fun y => ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame (l + r) t δ hδ) y)) from
    funext fun y => glyzPolarMeasure_powerAverage_eq_convolution A _ g q y]
  exact glyzPositiveConvolution_subspace_stable _ _ (g.continuous.measurable.enorm.pow_const q)
    (continuous_glyzPolarWeight A _).measurable.ennreal_ofReal
    (ENNReal.ofReal C) ENNReal.ofReal_ne_top (hweight t ht δ hδ hδ1) x

end PlanarNikodym
