import PlanarNikodym.Analysis.Fourier.GlyzNormalizedRawExtension
import PlanarNikodym.Analysis.Fourier.GlyzTimeTranslation

/-! A fixed finite collection of nonnegative time cutoffs is assembled
without any loss depending on the number of smooth leaf intervals.
The input need not be supported where the cutoffs sum to one: equality
is required only on the actual amplitude support. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

def glyzColorInput (w : ℝ → ℝ) (g : Plane → ℂ) (y : Plane) : ℂ :=
  (w y.1 : ℂ) * g y

theorem glyz_color_weight_le_one {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℝ) (hw : ∀ i t, 0 ≤ w i t) (hs : ∀ t, ∑ i, w i t ≤ 1)
    (i : ι) (t : ℝ) : w i t ≤ 1 := by
  classical
  exact (Finset.single_le_sum (fun j _ => hw j t) (Finset.mem_univ i)).trans (hs t)

theorem integrable_glyzColorInput {g : Plane → ℂ} (hg : Integrable g)
    (w : ℝ → ℝ) (hw : Continuous w) (hr : ∀ t, 0 ≤ w t ∧ w t ≤ 1) :
    Integrable (glyzColorInput w g) := by
  apply hg.bdd_mul (c := 1) ((Complex.continuous_ofReal.comp (hw.comp continuous_fst)).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖(w y.1 : ℂ)‖ ≤ (1 : ℝ)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr y.1).1] using (hr y.1).2

/-- Nonnegative cutoff weights preserve the total pointwise L¹ mass. -/
theorem glyzColorInput_enorm_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℝ) (hw : ∀ i t, 0 ≤ w i t) (hs : ∀ t, ∑ i, w i t ≤ 1)
    (g : Plane → ℂ) (y : Plane) : ∑ i, ‖glyzColorInput (w i) g y‖ₑ ≤ ‖g y‖ₑ := by
  classical
  have he (i : ι) : ‖glyzColorInput (w i) g y‖ₑ = ENNReal.ofReal (w i y.1) * ‖g y‖ₑ := by
    change ‖(w i y.1 : ℂ) * g y‖ₑ = _
    rw [enorm_mul]
    congr 1
    simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i y.1)]
  simp_rw [he]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i y.1)]
  have hh : ENNReal.ofReal (∑ i, w i y.1) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hs y.1)
  exact (mul_le_mul_left hh _).trans_eq (one_mul _)

theorem glyzColorInput_lintegral_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℝ) (hw : ∀ i, Continuous (w i))
    (hr : ∀ i t, 0 ≤ w i t) (hs : ∀ t, ∑ i, w i t ≤ 1)
    {g : Plane → ℂ} (hg : Integrable g) :
    (∑ i, ∫⁻ y, ‖glyzColorInput (w i) g y‖ₑ) ≤ ∫⁻ y, ‖g y‖ₑ := by
  classical
  have hi (i : ι) : Integrable (glyzColorInput (w i) g) :=
    integrable_glyzColorInput hg (w i) (hw i)
      (fun t => ⟨hr i t, glyz_color_weight_le_one w hr hs i t⟩)
  rw [← lintegral_finsetSum' Finset.univ (fun i _ => (hi i).aestronglyMeasurable.enorm)]
  exact lintegral_mono (glyzColorInput_enorm_sum_le w hr hs g)

theorem glyzColorInput_lintegral_rpow_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℝ) (hw : ∀ i, Continuous (w i))
    (hr : ∀ i t, 0 ≤ w i t) (hs : ∀ t, ∑ i, w i t ≤ 1)
    {g : Plane → ℂ} (hg : Integrable g) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, (∫⁻ y, ‖glyzColorInput (w i) g y‖ₑ) ^ p) ≤ (∫⁻ y, ‖g y‖ₑ) ^ p :=
  (glyz_ennreal_sum_rpow_le_rpow_sum Finset.univ _ hp).trans
    (ENNReal.rpow_le_rpow (glyzColorInput_lintegral_sum_le w hw hr hs hg) (zero_le_one.trans hp))

/-- Translating each color to its own fixed grid preserves its input
mass exactly. The bound is uniform in all selected shifts. -/
theorem glyz_shifted_color_lintegral_rpow_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℝ) (hw : ∀ i, Continuous (w i))
    (hr : ∀ i t, 0 ≤ w i t) (hs : ∀ t, ∑ i, w i t ≤ 1)
    (s : ι → ℝ) {g : Plane → ℂ} (hg : Integrable g) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, (∫⁻ y, ‖glyzTimeTranslateInput (glyzColorInput (w i) g) (s i) y‖ₑ) ^ p) ≤
      (∫⁻ y, ‖g y‖ₑ) ^ p := by
  simp_rw [lintegral_enorm_glyzTimeTranslateInput]
  exact glyzColorInput_lintegral_rpow_sum_le w hw hr hs hg hp

/-- The original raw extension is exactly reconstructed, even when the
original input extends beyond the cutoff region. -/
theorem glyzRawExtension_color_sum {P ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [Fintype ι] {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (w : ι → ℝ → ℝ) (hw : ∀ i, Continuous (w i))
    (hr : ∀ i t, 0 ≤ w i t) (hs : ∀ t, ∑ i, w i t ≤ 1)
    (hone : ∀ x t η, a (x, t, η) ≠ 0 → ∑ i, w i t = 1)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) (x : P) :
    (∑ i, glyzRawExtension Φ a (glyzColorInput (w i) g) r x) = glyzRawExtension Φ a g r x := by
  classical
  have hi (i : ι) : Integrable (glyzColorInput (w i) g) :=
    integrable_glyzColorInput hg (w i) (hw i)
      (fun t => ⟨hr i t, glyz_color_weight_le_one w hr hs i t⟩)
  simp_rw [glyzRawExtension_eq_compactKernel hΦ ha hc (hi _) r x]
  rw [glyzRawExtension_eq_compactKernel hΦ ha hc hg r x]
  have hiK (i : ι) : Integrable (fun y =>
      glyzColorInput (w i) g y * glyzRawKernel Φ a r (x, y)) :=
    integrable_compactKernel_smul volume (hi i) (contDiff_glyzRawKernel hΦ ha r)
      (hasCompactSupport_glyzRawKernel Φ hc r) x
  rw [← integral_finsetSum Finset.univ (fun i _ => hiK i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [glyzColorInput, ← Finset.sum_mul, ← Complex.ofReal_sum]
  by_cases hz : a (x, y) = 0
  · simp only [glyzRawKernel, hz, mul_zero]
  · rw [hone x y.1 y.2 hz, Complex.ofReal_one, one_mul]

/-- Power-triangle assembly over a fixed number of colors. Its cost is
independent of the number of smooth intervals in each color. -/
theorem glyzRawExtension_color_power_assembly {P ι : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [MeasurableSpace P] [BorelSpace P] [Fintype ι]
    (μ : Measure P) {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (w : ι → ℝ → ℝ) (hw : ∀ i, Continuous (w i))
    (hr : ∀ i t, 0 ≤ w i t) (hs : ∀ t, ∑ i, w i t ≤ 1)
    (hone : ∀ x t η, a (x, t, η) ≠ 0 → ∑ i, w i t = 1)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) {p : ℝ} (hp : 1 ≤ p)
    (D e : ℝ≥0∞) (E : ι → ℝ≥0∞)
    (hcolor : ∀ i, (∫⁻ x, ‖glyzRawExtension Φ a (glyzColorInput (w i) g) r x‖ₑ ^ p ∂μ) ≤
      D * E i + e * (∫⁻ y, ‖glyzColorInput (w i) g y‖ₑ) ^ p) :
    (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ p ∂μ) ≤
      (Fintype.card ι : ℝ≥0∞) ^ (p - 1) *
        (D * ∑ i, E i + e * (∫⁻ y, ‖g y‖ₑ) ^ p) := by
  classical
  let F := fun i => glyzRawExtension Φ a (glyzColorInput (w i) g) r
  have hm (i : ι) : Measurable (fun x => ‖F i x‖ₑ ^ p) :=
    (contDiff_glyzRawExtension hΦ ha hc (integrable_glyzColorInput hg (w i) (hw i)
      (fun t => ⟨hr i t, glyz_color_weight_le_one w hr hs i t⟩)) r).continuous.measurable.enorm.pow_const p
  calc
    _ ≤ ∫⁻ x, (Fintype.card ι : ℝ≥0∞) ^ (p - 1) * ∑ i, ‖F i x‖ₑ ^ p ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← glyzRawExtension_color_sum hΦ ha hc w hw hr hs hone hg r x]
      have h := ENNReal.rpow_sum_le_const_mul_sum_rpow Finset.univ (fun i => ‖F i x‖ₑ) hp
      exact (ENNReal.rpow_le_rpow (enorm_sum_le _ _) (zero_le_one.trans hp)).trans
        (by simpa only [Finset.card_univ] using h)
    _ = (Fintype.card ι : ℝ≥0∞) ^ (p - 1) * ∑ i, ∫⁻ x, ‖F i x‖ₑ ^ p ∂μ := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hm i),
        lintegral_finsetSum _ (fun i _ => hm i)]
    _ ≤ (Fintype.card ι : ℝ≥0∞) ^ (p - 1) *
        ∑ i, (D * E i + e * (∫⁻ y, ‖glyzColorInput (w i) g y‖ₑ) ^ p) := by
      gcongr with i hi
      exact hcolor i
    _ = (Fintype.card ι : ℝ≥0∞) ^ (p - 1) *
        (D * ∑ i, E i + e * ∑ i, (∫⁻ y, ‖glyzColorInput (w i) g y‖ₑ) ^ p) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
      gcongr
      exact glyzColorInput_lintegral_rpow_sum_le w hw hr hs hg hp

end PlanarNikodym
