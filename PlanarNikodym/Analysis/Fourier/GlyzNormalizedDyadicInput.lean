import PlanarNikodym.Analysis.Fourier.GlyzDyadicInput
import PlanarNikodym.Analysis.Fourier.TimeDataScaling

/-! Actual affine-normalized input pieces for a dyadic parent. The
original input is only assumed L¹: no representative-level measurable
hypothesis is needed for the change of variables. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal ContDiff
namespace PlanarNikodym

theorem integrable_glyzTimeDataRescaling {g : Plane → ℂ} (hg : Integrable g)
    (c : ℝ) {δ : ℝ} (hδ : δ ≠ 0) : Integrable (g ∘ timeDataRescaling c δ) := by
  have hmap : Integrable g (Measure.map (timeDataRescaling c δ) volume) := by
    rw [map_timeDataRescaling_volume c hδ]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact hmap.comp_measurable (by unfold timeDataRescaling; fun_prop)

/-- Exact L¹ scaling for arbitrary integrable data. -/
theorem lintegral_enorm_timeDataRescaling {g : Plane → ℂ} (hg : Integrable g)
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ y, ‖g (timeDataRescaling c δ y)‖ₑ) =
      ENNReal.ofReal δ⁻¹ * ∫⁻ y, ‖g y‖ₑ := by
  have hmap : Integrable g (Measure.map (timeDataRescaling c δ) volume) := by
    rw [map_timeDataRescaling_volume c hδ.ne']
    exact hg.smul_measure ENNReal.ofReal_ne_top
  rw [← lintegral_map' hmap.aestronglyMeasurable.enorm
    (show AEMeasurable (timeDataRescaling c δ) volume by
      apply Measurable.aemeasurable; unfold timeDataRescaling; fun_prop),
    map_timeDataRescaling_volume c hδ.ne', lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr hδ)]
  rfl

def glyzNormalizedDyadicInput (n q i j : ℕ) (g : Plane → ℂ) : Plane → ℂ :=
  glyzDyadicInput (n + q) (i * 2 ^ q + j) g ∘
    timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n)

theorem integrable_glyzNormalizedDyadicInput {g : Plane → ℂ} (hg : Integrable g)
    (n q i j : ℕ) : Integrable (glyzNormalizedDyadicInput n q i j g) :=
  integrable_glyzTimeDataRescaling (integrable_glyzDyadicInput hg _ _) _ (glyzDyadicScale_pos n).ne'

theorem glyzNormalizedDyadicInput_lintegral_enorm {g : Plane → ℂ} (hg : Integrable g)
    (n q i j : ℕ) :
    (∫⁻ y, ‖glyzNormalizedDyadicInput n q i j g y‖ₑ) =
      ENNReal.ofReal (glyzDyadicScale n)⁻¹ *
        ∫⁻ y, ‖glyzDyadicInput (n + q) (i * 2 ^ q + j) g y‖ₑ :=
  lintegral_enorm_timeDataRescaling (integrable_glyzDyadicInput hg _ _) _ (glyzDyadicScale_pos n)

theorem glyzDyadicLeft_child_affine (n q i j : ℕ) :
    glyzDyadicLeft (n + q) (i * 2 ^ q + j) =
      glyzDyadicLeft n i + glyzDyadicScale n * glyzDyadicLeft q j := by
  have hq : glyzDyadicScale q * (2 : ℝ) ^ q = 1 := inv_mul_cancel₀ (by positivity)
  unfold glyzDyadicLeft
  rw [glyzDyadicScale_add]
  push_cast
  calc
    _ = glyzDyadicScale n * i * (glyzDyadicScale q * (2 : ℝ) ^ q) +
        glyzDyadicScale n * (glyzDyadicScale q * j) := by ring
    _ = _ := by rw [hq]; ring

theorem glyzDyadicRight_child_affine (n q i j : ℕ) :
    glyzDyadicRight (n + q) (i * 2 ^ q + j) =
      glyzDyadicLeft n i + glyzDyadicScale n * glyzDyadicRight q j := by
  have hq : glyzDyadicScale q * (2 : ℝ) ^ q = 1 := inv_mul_cancel₀ (by positivity)
  unfold glyzDyadicRight glyzDyadicLeft
  rw [glyzDyadicScale_add]
  push_cast
  calc
    _ = glyzDyadicScale n * i * (glyzDyadicScale q * (2 : ℝ) ^ q) +
        glyzDyadicScale n * (glyzDyadicScale q * (j + 1)) := by ring
    _ = _ := by rw [hq]; ring

theorem glyzDyadicInputSet_affine_iff (n q i j : ℕ) (y : Plane) :
    timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n) y ∈
      glyzDyadicInputSet (n + q) (i * 2 ^ q + j) ↔ y ∈ glyzDyadicInputSet q j := by
  change glyzDyadicLeft (n + q) (i * 2 ^ q + j) ≤ _ ∧
    _ < glyzDyadicRight (n + q) (i * 2 ^ q + j) ↔ _
  rw [glyzDyadicLeft_child_affine, glyzDyadicRight_child_affine]
  change (_ + glyzDyadicScale n * glyzDyadicLeft q j ≤ _ + glyzDyadicScale n * y.1 ∧
    _ + glyzDyadicScale n * y.1 < _ + glyzDyadicScale n * glyzDyadicRight q j) ↔
    (glyzDyadicLeft q j ≤ y.1 ∧ y.1 < glyzDyadicRight q j)
  simp only [add_le_add_iff_left, add_lt_add_iff_left,
    mul_le_mul_iff_right₀ (glyzDyadicScale_pos n), mul_lt_mul_iff_right₀ (glyzDyadicScale_pos n)]

/-- The normalized pieces are exactly the standard dyadic restrictions
of the normalized original data. -/
theorem glyzNormalizedDyadicInput_eq (g : Plane → ℂ) (n q i j : ℕ) :
    glyzNormalizedDyadicInput n q i j g =
      glyzDyadicInput q j (g ∘ timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n)) := by
  funext y
  have h := glyzDyadicInputSet_affine_iff n q i j y
  simp only [glyzNormalizedDyadicInput, Function.comp_apply, glyzDyadicInput,
    Set.indicator]
  split_ifs <;> simp_all

/-- Exact parent reconstruction in normalized coordinates. -/
theorem glyzNormalizedDyadicInput_sum (g : Plane → ℂ) (n q i : ℕ) :
    (∑ j ∈ Finset.range (2 ^ q), glyzNormalizedDyadicInput n q i j g) =
      glyzDyadicInput n i g ∘ timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n) := by
  rw [glyzDyadicInput_refine g n q i]
  funext y
  simp only [glyzNormalizedDyadicInput, Function.comp_apply, Finset.sum_apply]

/-- Exact normalized parent L¹ mass equals the sum of child masses. -/
theorem glyzNormalizedDyadicInput_lintegral_enorm_sum {g : Plane → ℂ} (hg : Integrable g)
    (n q i : ℕ) :
    (∑ j ∈ Finset.range (2 ^ q), ∫⁻ y, ‖glyzNormalizedDyadicInput n q i j g y‖ₑ) =
      ENNReal.ofReal (glyzDyadicScale n)⁻¹ * ∫⁻ y, ‖glyzDyadicInput n i g y‖ₑ := by
  simp_rw [glyzNormalizedDyadicInput_lintegral_enorm hg]
  rw [← Finset.mul_sum, ← glyzDyadicInput_lintegral_enorm_refine hg]

/-- Half-open time support is exact; radial support is unchanged. -/
theorem support_glyzNormalizedDyadicInput {g : Plane → ℂ} {J : Set ℝ}
    (hs : Function.support g ⊆ {y | y.2 ∈ J}) (n q i j : ℕ) :
    Function.support (glyzNormalizedDyadicInput n q i j g) ⊆
      Ico (glyzDyadicLeft q j) (glyzDyadicRight q j) ×ˢ J := by
  rw [glyzNormalizedDyadicInput_eq]
  intro y hy
  have hi : y ∈ glyzDyadicInputSet q j := by
    by_contra hh
    have hz : glyzDyadicInput q j
        (g ∘ timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n)) y = 0 := by
      simp [glyzDyadicInput, hh]
    exact hy hz
  have hg : g (timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n) y) ≠ 0 := by
    simpa [Function.mem_support, glyzDyadicInput, hi] using hy
  have hrad := hs (show timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n) y ∈
    Function.support g from hg)
  exact ⟨hi, hrad⟩

/-- The actual closed support lies in the compact dyadic rectangle. -/
theorem tsupport_glyzNormalizedDyadicInput {g : Plane → ℂ} {J : Set ℝ}
    (hJ : IsClosed J) (hs : Function.support g ⊆ {y | y.2 ∈ J}) (n q i j : ℕ) :
    tsupport (glyzNormalizedDyadicInput n q i j g) ⊆
      Icc (glyzDyadicLeft q j) (glyzDyadicRight q j) ×ˢ J := by
  apply closure_minimal _ (isClosed_Icc.prod hJ)
  intro y hy
  have h := support_glyzNormalizedDyadicInput hs n q i j hy
  exact ⟨⟨h.1.1, h.1.2.le⟩, h.2⟩

/-- Real-valued L¹ mass, for direct use with Bochner error estimates. -/
theorem integral_norm_timeDataRescaling {g : Plane → ℂ} (hg : Integrable g)
    (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y, ‖g (timeDataRescaling c δ y)‖) = δ⁻¹ * ∫ y, ‖g y‖ := by
  have hh := integrable_glyzTimeDataRescaling hg c hδ.ne'
  change Integrable (fun y => g (timeDataRescaling c δ y)) at hh
  have he := lintegral_enorm_timeDataRescaling hg c hδ
  rw [← ofReal_integral_norm_eq_lintegral_enorm hh,
    ← ofReal_integral_norm_eq_lintegral_enorm hg, ← ENNReal.ofReal_mul (inv_nonneg.mpr hδ.le)] at he
  exact ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => norm_nonneg _)
    (mul_nonneg (inv_nonneg.mpr hδ.le) (integral_nonneg fun _ => norm_nonneg _)) |>.mp he

theorem glyzNormalizedDyadicInput_integral_norm {g : Plane → ℂ} (hg : Integrable g)
    (n q i j : ℕ) :
    (∫ y, ‖glyzNormalizedDyadicInput n q i j g y‖) =
      (glyzDyadicScale n)⁻¹ * ∫ y, ‖glyzDyadicInput (n + q) (i * 2 ^ q + j) g y‖ :=
  integral_norm_timeDataRescaling (integrable_glyzDyadicInput hg _ _) _ (glyzDyadicScale_pos n)

theorem hasCompactSupport_glyzNormalizedDyadicInput {g : Plane → ℂ} {J : Set ℝ}
    (hJ : IsCompact J) (hs : Function.support g ⊆ {y | y.2 ∈ J}) (n q i j : ℕ) :
    HasCompactSupport (glyzNormalizedDyadicInput n q i j g) :=
  (isCompact_Icc.prod hJ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_glyzNormalizedDyadicInput hJ.isClosed hs n q i j)

/-- Actual compact-kernel reconstruction after parent normalization. -/
theorem glyz_normalized_compactKernel_refine {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : Plane → ℂ} (hg : Integrable g) {H : X × Plane → ℂ}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (n q i : ℕ) (x : X) :
    (∫ y, glyzDyadicInput n i g
      (timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n) y) * H (x, y)) =
      ∑ j ∈ Finset.range (2 ^ q), ∫ y, glyzNormalizedDyadicInput n q i j g y * H (x, y) := by
  have hsum := glyzNormalizedDyadicInput_sum g n q i
  change (∫ y, (glyzDyadicInput n i g ∘
    timeDataRescaling (glyzDyadicLeft n i) (glyzDyadicScale n)) y * H (x, y)) = _
  rw [← hsum]
  simp only [Finset.sum_apply, Finset.sum_mul]
  apply integral_finsetSum
  intro j hj
  exact integrable_compactKernel_smul volume (integrable_glyzNormalizedDyadicInput hg n q i j) hH hc x

@[simp] theorem norm_glyzDyadicInput (g : Plane → ℂ) (n i : ℕ) (y : Plane) :
    ‖glyzDyadicInput n i g y‖ = glyzDyadicInput n i (fun z => ‖g z‖) y := by
  by_cases hy : y ∈ glyzDyadicInputSet n i <;> simp [glyzDyadicInput, hy]

theorem glyzDyadicInput_integral_norm_refine {g : Plane → ℂ} (hg : Integrable g)
    (n q i : ℕ) :
    (∫ y, ‖glyzDyadicInput n i g y‖) =
      ∑ j ∈ Finset.range (2 ^ q), ∫ y, ‖glyzDyadicInput (n + q) (i * 2 ^ q + j) g y‖ := by
  simp only [norm_glyzDyadicInput]
  rw [glyzDyadicInput_refine]
  simp only [Finset.sum_apply]
  apply integral_finsetSum
  intro j hj
  exact hg.norm.indicator (measurableSet_glyzDyadicInputSet _ _)

theorem glyzNormalizedDyadicInput_integral_norm_sum {g : Plane → ℂ} (hg : Integrable g)
    (n q i : ℕ) :
    (∑ j ∈ Finset.range (2 ^ q), ∫ y, ‖glyzNormalizedDyadicInput n q i j g y‖) =
      (glyzDyadicScale n)⁻¹ * ∫ y, ‖glyzDyadicInput n i g y‖ := by
  simp_rw [glyzNormalizedDyadicInput_integral_norm hg]
  rw [← Finset.mul_sum, ← glyzDyadicInput_integral_norm_refine hg]

theorem glyzDyadicInterval_dist_center (q j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (glyzDyadicLeft q j) (glyzDyadicRight q j)) :
    |t - glyzDyadicCenter q j| ≤ glyzDyadicScale q := by
  have h := glyzDyadicScale_pos q
  dsimp [glyzDyadicLeft, glyzDyadicRight] at ht
  unfold glyzDyadicCenter
  exact abs_le.mpr ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩

end PlanarNikodym
