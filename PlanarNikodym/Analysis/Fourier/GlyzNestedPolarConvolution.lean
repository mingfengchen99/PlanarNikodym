import PlanarNikodym.Analysis.Fourier.GlyzNestedMomentGeometry
import PlanarNikodym.Analysis.Fourier.GlyzRelativeWeight
import PlanarNikodym.Analysis.Fourier.GlyzWeightedConvolution

/-! GLYZ v3 Appendix A.1 for actual moment-curve polar weights, with
arbitrary parent centers and scales and different child centers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

/-- No constants depend on either interval, their ratio, or the point. -/
theorem exists_uniform_glyz_nested_polar_convolution (m A : ℕ)
    (hA : m < A) (hQ : m * (m + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c κ s ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ),
      s ∈ Icc (-1 : ℝ) 1 → ρ ≤ 1 → ∀ x : GlyzSpace m,
      (∫ y, glyzPolarWeight A (glyzMomentFrequencyFrame m c κ hκ) (x - y) *
        glyzPolarWeight A (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)) y) ≤
      C * glyzPolarWeight A (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)) x := by
  obtain ⟨D, hD, hcoords⟩ := exists_uniform_glyzMomentCoordinates_nested m
  let M := ((2 : ℝ) ^ m)⁻¹ * ∫ y : Base m, glyzDecayWeight A y
  have hM : 0 ≤ M := mul_nonneg (by positivity)
    (integral_nonneg fun y => (glyzDecayWeight_pos A y).le)
  let C := 2 ^ (A + 1) * D ^ A * M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1 + C, by positivity, ?_⟩
  intro c κ s ρ hκ hρ hs hρ1 x
  have hp : (D * ρ) ^ A * |LinearMap.det (glyzMomentFrequencyFrame m c κ hκ).toLinearMap| ≤
      D ^ A * |LinearMap.det
        (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)).toLinearMap| := by
    rw [det_glyzMomentFrequencyFrame m c κ hκ,
      det_glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)]
    simp only [mul_pow, abs_mul, abs_of_pos (pow_pos hκ _), abs_of_pos (pow_pos hρ _)]
    have hp := pow_le_pow_of_le_one hρ.le hρ1 hQ
    calc
      _ = (D ^ A * κ ^ (m * (m + 1) / 2) *
          |LinearMap.det (glyzMomentFrequencyFrame m 0 1 zero_lt_one).toLinearMap|) * ρ ^ A := by ring
      _ ≤ (D ^ A * κ ^ (m * (m + 1) / 2) *
          |LinearMap.det (glyzMomentFrequencyFrame m 0 1 zero_lt_one).toLinearMap|) *
          ρ ^ (m * (m + 1) / 2) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have h := integral_glyzPolarWeight_convolution_le hA
    (glyzMomentFrequencyFrame m c κ hκ)
    (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ))
    (show 0 ≤ D * ρ by positivity) (one_le_pow₀ hD) hp
    (hcoords c κ s ρ hκ hρ hs hρ1) x
  exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [C, M]; linarith)
    (glyzPolarWeight_pos A _ x).le)

/-- The same estimate in the positive-convolution API used by the
bilinear proof. The conversion is justified by actual integrability. -/
theorem exists_uniform_glyz_nested_positive_convolution (m A : ℕ)
    (hA : m < A) (hQ : m * (m + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c κ s ρ : ℝ) (hκ : 0 < κ) (hρ : 0 < ρ),
      s ∈ Icc (-1 : ℝ) 1 → ρ ≤ 1 → ∀ x : GlyzSpace m,
      glyzPositiveConvolution
        (fun y => ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame m c κ hκ) y))
        (fun y => ENNReal.ofReal (glyzPolarWeight A
          (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)) y)) x ≤
      ENNReal.ofReal C * ENNReal.ofReal (glyzPolarWeight A
        (glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)) x) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_glyz_nested_polar_convolution m A hA hQ
  refine ⟨C, hC, ?_⟩
  intro c κ s ρ hκ hρ hs hρ1 x
  let L₁ := glyzMomentFrequencyFrame m c κ hκ
  let L₂ := glyzMomentFrequencyFrame m (c + κ * s) (κ * ρ) (mul_pos hκ hρ)
  have hint : Integrable (fun y => glyzPolarWeight A L₁ (x - y) * glyzPolarWeight A L₂ y) := by
    apply ((integrable_glyzPolarWeight hA L₂).const_mul
      (((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L₁.toLinearMap|)).mono'
      (((continuous_glyzPolarWeight A L₁).comp (continuous_const.sub continuous_id)).mul
        (continuous_glyzPolarWeight A L₂)).aestronglyMeasurable
    filter_upwards [] with y
    change |glyzPolarWeight A L₁ (x - y) * glyzPolarWeight A L₂ y| ≤ _
    rw [abs_of_pos (mul_pos (glyzPolarWeight_pos A L₁ _) (glyzPolarWeight_pos A L₂ _))]
    apply mul_le_mul_of_nonneg_right _ (glyzPolarWeight_pos A L₂ y).le
    unfold glyzPolarWeight glyzBoxWeight
    nlinarith [glyzDecayWeight_le_one A (glyzBoxCoordinates L₁ (x - y)),
      show 0 ≤ ((2 : ℝ) ^ m)⁻¹ * |LinearMap.det L₁.toLinearMap| by positivity]
  rw [glyzPositiveConvolution_comm]
  change (∫⁻ y, ENNReal.ofReal (glyzPolarWeight A L₁ (x - y)) *
    ENNReal.ofReal (glyzPolarWeight A L₂ y)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (glyzPolarWeight A L₂ x)
  simp_rw [← ENNReal.ofReal_mul (glyzPolarWeight_pos A L₁ _).le]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => (mul_pos (glyzPolarWeight_pos A L₁ _) (glyzPolarWeight_pos A L₂ _)).le),
    ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal (h c κ s ρ hκ hρ hs hρ1 x)

/-- A version stated directly in terms of the two actual centers and
lengths. The hypotheses include every pair of nested closed intervals. -/
theorem exists_uniform_glyz_nested_interval_convolution (m A : ℕ)
    (hA : m < A) (hQ : m * (m + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c d κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η),
      |d - c| ≤ κ → η ≤ κ → ∀ x : GlyzSpace m,
      glyzPositiveConvolution
        (fun y => ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame m c κ hκ) y))
        (fun y => ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame m d η hη) y)) x ≤
      ENNReal.ofReal C * ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame m d η hη) x) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_glyz_nested_positive_convolution m A hA hQ
  refine ⟨C, hC, ?_⟩
  intro c d κ η hκ hη hc hηκ x
  have hs : (d - c) / κ ∈ Icc (-1 : ℝ) 1 := by
    have hc' := abs_le.mp hc
    constructor
    · apply (le_div_iff₀ hκ).mpr
      linarith
    · apply (div_le_iff₀ hκ).mpr
      linarith
  have hρ : 0 < η / κ := div_pos hη hκ
  have hρ1 : η / κ ≤ 1 := (div_le_one hκ).mpr hηκ
  have he₁ : c + κ * ((d - c) / κ) = d := by field_simp; ring
  have he₂ : κ * (η / κ) = η := mul_div_cancel₀ η hκ.ne'
  have hh := h c κ ((d - c) / κ) (η / κ) hκ hρ hs hρ1 x
  simpa only [he₁, he₂] using hh

/-- Actual inclusion of the centered closed intervals implies the
numerical hypotheses used by the convolution theorem. -/
theorem glyz_nested_closedInterval_bounds {c d κ η : ℝ}
    (hκ : 0 < κ) (hη : 0 < η)
    (h : Icc (d - η / 2) (d + η / 2) ⊆ Icc (c - κ / 2) (c + κ / 2)) :
    |d - c| ≤ κ ∧ η ≤ κ := by
  have hd := h (show d ∈ Icc (d - η / 2) (d + η / 2) from ⟨by linarith, by linarith⟩)
  have hl := h (show d - η / 2 ∈ Icc (d - η / 2) (d + η / 2) from ⟨le_rfl, by linarith⟩)
  have hr := h (show d + η / 2 ∈ Icc (d - η / 2) (d + η / 2) from ⟨by linarith, le_rfl⟩)
  exact ⟨abs_le.mpr ⟨by linarith [hd.1], by linarith [hd.2]⟩, by linarith [hl.1, hr.2]⟩

/-- Appendix A.1, stated with actual set-theoretic interval nesting. -/
theorem exists_uniform_glyz_closedInterval_convolution (m A : ℕ)
    (hA : m < A) (hQ : m * (m + 1) / 2 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c d κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η),
      Icc (d - η / 2) (d + η / 2) ⊆ Icc (c - κ / 2) (c + κ / 2) →
      ∀ x : GlyzSpace m,
      glyzPositiveConvolution
        (fun y => ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame m c κ hκ) y))
        (fun y => ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame m d η hη) y)) x ≤
      ENNReal.ofReal C * ENNReal.ofReal (glyzPolarWeight A (glyzMomentFrequencyFrame m d η hη) x) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_glyz_nested_interval_convolution m A hA hQ
  refine ⟨C, hC, ?_⟩
  intro c d κ η hκ hη hsub x
  have hb := glyz_nested_closedInterval_bounds hκ hη hsub
  exact h c d κ η hκ hη hb.1 hb.2 x

end PlanarNikodym
