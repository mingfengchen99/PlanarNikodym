import PlanarNikodym.Analysis.Fourier.GlyzSmoothColorAssembly
import PlanarNikodym.Analysis.Localization.ScaleTimePartition

/-! The final time pieces use one fixed smooth window on the exact
requested scale. A finite telescoping sum covers the paper's time
interval; its cutoff derivatives are uniformly controlled by the
already proved scaleTimeCutoff estimates. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

def glyzExactTimeCount (δ : ℝ) : ℕ := ⌈2 / δ⌉₊ + 1

theorem glyzExactTimeCount_bound {δ : ℝ} (hδ : 0 < δ) :
    (glyzExactTimeCount δ : ℝ) < 2 / δ + 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 2 / δ by positivity)
  simpa only [glyzExactTimeCount, Nat.cast_add, Nat.cast_one] using
    (show (⌈2 / δ⌉₊ : ℝ) + 1 < 2 / δ + 2 by linarith)

theorem glyzExactTimeCount_low {δ : ℝ} (hδ : (1 / 256 : ℝ) ≤ δ) :
    glyzExactTimeCount δ ≤ 514 := by
  have hδ0 : 0 < δ := lt_of_lt_of_le (by norm_num) hδ
  have hdiv : 2 / δ ≤ (512 : ℝ) := (div_le_iff₀ hδ0).mpr (by nlinarith)
  have hb := glyzExactTimeCount_bound hδ0
  exact_mod_cast (show (glyzExactTimeCount δ : ℝ) ≤ 514 by linarith)

theorem glyz_sum_scaleTimeCutoff_le_one (a δ t : ℝ) (M : ℕ) :
    ∑ i ∈ Finset.range M, scaleTimeCutoff a δ i t ≤ 1 := by
  rw [sum_scaleTimeCutoff]
  linarith [Real.smoothTransition.le_one ((t - a) / δ + 1),
    Real.smoothTransition.nonneg ((t - a) / δ + 1 - M)]

theorem glyzExactTimePartition_sum {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∑ i ∈ Finset.range (glyzExactTimeCount δ), scaleTimeCutoff (-1) δ i t = 1 := by
  apply sum_scaleTimeCutoff_eq_one (-1) hδ
  refine ⟨ht.1, ?_⟩
  have hceil : (2 : ℝ) / δ ≤ ⌈2 / δ⌉₊ := Nat.le_ceil _
  have hcover : (2 : ℝ) ≤ (⌈2 / δ⌉₊ : ℝ) * δ := (div_le_iff₀ hδ).mp hceil
  simp only [glyzExactTimeCount, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  linarith [ht.2]

theorem glyzExactTimePartition_fin_sum {δ : ℝ} (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∑ i : Fin (glyzExactTimeCount δ), scaleTimeCutoff (-1) δ i t = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => scaleTimeCutoff (-1) δ i t)]
  exact glyzExactTimePartition_sum hδ ht

theorem glyzExactTimePartition_fin_sum_le_one (δ t : ℝ) :
    ∑ i : Fin (glyzExactTimeCount δ), scaleTimeCutoff (-1) δ i t ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => scaleTimeCutoff (-1) δ i t)]
  exact glyz_sum_scaleTimeCutoff_le_one _ _ _ _

def glyzExactTimePiece (δ : ℝ) (i : ℕ) (g : Plane → ℂ) : Plane → ℂ :=
  glyzColorInput (scaleTimeCutoff (-1) δ i) g

theorem integrable_glyzExactTimePiece {g : Plane → ℂ} (hg : Integrable g)
    (δ : ℝ) (i : ℕ) : Integrable (glyzExactTimePiece δ i g) :=
  integrable_glyzColorInput hg _ (contDiff_scaleTimeCutoff _ _ _).continuous
    (fun _ => ⟨scaleTimeCutoff_nonneg _ _ _ _, scaleTimeCutoff_le_one _ _ _ _⟩)

/-- An auxiliary fixed time cutoff equal to one on the amplitude has
no effect on the original operator, even for nonsmooth input data. -/
theorem glyzRawExtension_time_cutoff {P : Type} (Φ : P × ℝ → ℝ)
    (a : P × Plane → ℂ) (χ : ℝ → ℝ)
    (hone : ∀ x t η, a (x, t, η) ≠ 0 → χ t = 1)
    (g : Plane → ℂ) (r : ℝ) :
    glyzRawExtension Φ a (glyzColorInput χ g) r = glyzRawExtension Φ a g r := by
  funext x
  unfold glyzRawExtension
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hz : a (x, t, η) = 0
  · simp only [hz, mul_zero, zero_mul]
  · simp only [glyzColorInput, hone x t η hz, Complex.ofReal_one, one_mul]

theorem glyzRawExtension_exactTimePiece_localize {P : Type} (Φ : P × ℝ → ℝ)
    (a : P × Plane → ℂ) (χ : ℝ → ℝ)
    (hone : ∀ x t η, a (x, t, η) ≠ 0 → χ t = 1)
    (g : Plane → ℂ) (r δ : ℝ) (i : ℕ) :
    glyzRawExtension Φ a (glyzColorInput (fun t => χ t * scaleTimeCutoff (-1) δ i t) g) r =
      glyzRawExtension Φ a (glyzExactTimePiece δ i g) r := by
  have he : glyzColorInput (fun t => χ t * scaleTimeCutoff (-1) δ i t) g =
      glyzColorInput χ (glyzExactTimePiece δ i g) := by
    funext y
    simp only [glyzColorInput, glyzExactTimePiece, Complex.ofReal_mul, mul_assoc]
  rw [he]
  exact glyzRawExtension_time_cutoff Φ a χ hone _ r

theorem glyzRawExtension_exactTimePiece_eq_timeSliceExtension {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × Plane → ℂ) (g : Plane → ℂ)
    (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) :
    glyzRawExtension Φ a (glyzExactTimePiece δ i g) r =
      timeSliceExtension Φ a g r (-1 + (i : ℝ) * δ) δ := by
  funext x
  unfold glyzRawExtension timeSliceExtension
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  have he : (t - (-1 : ℝ)) / δ - i = (t - (-1 + (i : ℝ) * δ)) / δ := by
    field_simp
    ring
  simp only [glyzExactTimePiece, glyzColorInput, scaleTimeCutoff, he]
  ring

/-- The bounded-frequency regime only needs the genuine finite sum
inequality. Its cost is the number of actual standard time pieces. -/
theorem glyzRawExtension_exactTimePartition_power {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → t ∈ Icc (-1 : ℝ) 1)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ)
    {δ p : ℝ} (hδ : 0 < δ) (hp : 1 ≤ p) :
    (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ p ∂μ) ≤
      (glyzExactTimeCount δ : ℝ≥0∞) ^ (p - 1) *
        ∑ i : Fin (glyzExactTimeCount δ),
          ∫⁻ x, ‖glyzRawExtension Φ a (glyzExactTimePiece δ i g) r x‖ₑ ^ p ∂μ := by
  let w := fun i : Fin (glyzExactTimeCount δ) => scaleTimeCutoff (-1) δ i
  let E := fun i : Fin (glyzExactTimeCount δ) =>
    ∫⁻ x, ‖glyzRawExtension Φ a (glyzExactTimePiece δ i g) r x‖ₑ ^ p ∂μ
  have h := glyzRawExtension_color_power_assembly μ hΦ ha hc w
    (fun _ => (contDiff_scaleTimeCutoff _ _ _).continuous)
    (fun _ _ => scaleTimeCutoff_nonneg _ _ _ _)
    (fun t => glyzExactTimePartition_fin_sum_le_one δ t)
    (fun x t η hn => glyzExactTimePartition_fin_sum hδ (has x t η hn))
    hg r hp 1 0 E (fun _ => by simp only [E, glyzExactTimePiece, one_mul, zero_mul, add_zero]; rfl)
  simpa only [Fintype.card_fin, one_mul, zero_mul, add_zero] using h

end PlanarNikodym
