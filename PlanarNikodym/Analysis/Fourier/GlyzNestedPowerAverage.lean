import PlanarNikodym.Analysis.Fourier.GlyzNestedPolarConvolution

/-! The nested-interval convolution estimate on the actual Schwartz
powers in Lemma 3.8, including removal of the larger interval weight. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform
open scoped ENNReal NNReal FourierTransform
namespace PlanarNikodym

theorem glyzPolarMeasure_subspaceAverage {m : ℕ} (A : ℕ)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) {F : GlyzSpace m → ℝ≥0∞}
    (hF : Measurable F) (x : GlyzSpace m) :
    glyzSubspaceAverage (glyzPolarMeasure A L) (ContinuousLinearMap.id ℝ (GlyzSpace m)) F x =
      glyzPositiveConvolution (fun y => ENNReal.ofReal (glyzPolarWeight A L y)) F x := by
  unfold glyzSubspaceAverage glyzPolarMeasure glyzPositiveConvolution
  simp only [ContinuousLinearMap.id_apply]
  exact lintegral_withDensity_eq_lintegral_mul volume
    (continuous_glyzPolarWeight A L).measurable.ennreal_ofReal
    (hF.comp (continuous_const.sub continuous_id).measurable)

/-- The extra parent polar weight can be removed from the actual child
power average. The constant is uniform in the function and exponent. -/
theorem exists_uniform_glyz_nested_powerAverage (m A : ℕ)
    (hA : m < A) (hQ : m * (m + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c d κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η),
      |d - c| ≤ κ → η ≤ κ →
      ∀ (f : SchwartzMap (GlyzSpace m) ℂ) (p : ℝ) (x : GlyzSpace m),
      glyzSubspaceAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame m c κ hκ))
        (ContinuousLinearMap.id ℝ (GlyzSpace m))
        (glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame m d η hη)) f p) x ≤
      ENNReal.ofReal C *
        glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame m d η hη)) f p x := by
  obtain ⟨C, hC, hweight⟩ := exists_uniform_glyz_nested_interval_convolution m A hA hQ
  refine ⟨C, hC, ?_⟩
  intro c d κ η hκ hη hc hηκ f p x
  let L₁ := glyzMomentFrequencyFrame m c κ hκ
  let L₂ := glyzMomentFrequencyFrame m d η hη
  letI := isFiniteMeasure_glyzPolarMeasure hA L₁
  have hstable (z : GlyzSpace m) :
      glyzSubspaceAverage (glyzPolarMeasure A L₁) (ContinuousLinearMap.id ℝ (GlyzSpace m))
        (fun y => ENNReal.ofReal (glyzPolarWeight A L₂ y)) z ≤
      ENNReal.ofReal C * ENNReal.ofReal (glyzPolarWeight A L₂ z) := by
    rw [glyzPolarMeasure_subspaceAverage A L₁ (continuous_glyzPolarWeight A L₂).measurable.ennreal_ofReal]
    exact hweight c d κ η hκ hη hc hηκ z
  rw [show glyzPowerAverage (glyzPolarMeasure A L₂) f p =
      glyzPositiveConvolution (fun y => ‖f y‖ₑ ^ p)
        (fun y => ENNReal.ofReal (glyzPolarWeight A L₂ y)) from
      funext fun y => glyzPolarMeasure_powerAverage_eq_convolution A L₂ f p y]
  exact glyzPositiveConvolution_subspace_stable _ _ (f.continuous.measurable.enorm.pow_const p)
    (continuous_glyzPolarWeight A L₂).measurable.ennreal_ofReal
    (ENNReal.ofReal C) ENNReal.ofReal_ne_top hstable x

/-- The uncertainty principle followed by Appendix A.1 replaces the
parent polar weight by the child's own weight, for every Fourier-supported
Schwartz piece. This is the final weight replacement in Lemma 3.8. -/
theorem exists_uniform_glyz_parent_powerAverage_le_child (m A : ℕ)
    (hA : m < A) (hQ : m * (m + 1) / 2 ≤ A) {p : ℝ≥0} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c d κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η),
      |d - c| ≤ κ → η ≤ κ → ∀ f : SchwartzMap (GlyzSpace m) ℂ,
      Function.support (𝓕 (f : GlyzSpace m → ℂ)) ⊆ glyzMomentFrequencyBox m d η hη →
      ∀ x : GlyzSpace m,
      glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame m c κ hκ)) f (p : ℝ) x ≤
      ENNReal.ofReal C *
        glyzPowerAverage (glyzPolarMeasure A (glyzMomentFrequencyFrame m d η hη)) f (p : ℝ) x := by
  obtain ⟨C, hC, hnest⟩ := exists_uniform_glyz_nested_powerAverage m A hA hQ
  obtain ⟨U, hU, hunc⟩ := glyz_moment_uncertainty m A hp
  refine ⟨U * C, mul_pos hU hC, ?_⟩
  intro c d κ η hκ hη hc hηκ f hs x
  let L₁ := glyzMomentFrequencyFrame m c κ hκ
  let L₂ := glyzMomentFrequencyFrame m d η hη
  have hu (z : GlyzSpace m) : ‖f z‖ₑ ^ (p : ℝ) ≤
      ENNReal.ofReal U * glyzPowerAverage (glyzPolarMeasure A L₂) f (p : ℝ) z := by
    rw [glyzPolarMeasure_average]
    exact hunc d η hη f hs z
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal U * glyzPowerAverage (glyzPolarMeasure A L₂) f (p : ℝ) (x - y)
        ∂glyzPolarMeasure A L₁ := lintegral_mono fun y => hu (x - y)
    _ = ENNReal.ofReal U * glyzSubspaceAverage (glyzPolarMeasure A L₁)
        (ContinuousLinearMap.id ℝ (GlyzSpace m))
        (glyzPowerAverage (glyzPolarMeasure A L₂) f (p : ℝ)) x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal U * (ENNReal.ofReal C *
        glyzPowerAverage (glyzPolarMeasure A L₂) f (p : ℝ) x) :=
      mul_le_mul' le_rfl (hnest c d κ η hκ hη hc hηκ f (p : ℝ) x)
    _ = _ := by rw [ENNReal.ofReal_mul hU.le, mul_assoc]

end PlanarNikodym
