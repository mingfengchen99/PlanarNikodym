import PlanarNikodym.Analysis.Fourier.GlyzFrequencyBoxes

/-! Actual smooth Fourier projections on Schwartz space, with their
reproduction, support, uniform kernel mass, and power-integral bounds. -/
noncomputable section
open Set Metric MeasureTheory FourierTransform
open scoped FourierTransform Convolution ENNReal NNReal BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzFourierProjector (χ : SchwartzMap E ℂ) :
    SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap E ℂ :=
  (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ).flip
    (glyzReproducingKernel χ)).toLinearMap

theorem glyzFourierProjector_apply (χ f : SchwartzMap E ℂ) :
    glyzFourierProjector χ f =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f (glyzReproducingKernel χ) :=
  SchwartzMap.convolution_flip _ _ _

theorem glyzFourierProjector_apply_apply (χ f : SchwartzMap E ℂ) (x : E) :
    glyzFourierProjector χ f x =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] glyzReproducingKernel χ) x := by
  rw [glyzFourierProjector_apply, SchwartzMap.convolution_apply]

theorem glyzFourierProjector_reproduces (χ f : SchwartzMap E ℂ)
    (hχ : ∀ ξ ∈ Function.support (𝓕 (f : E → ℂ)), χ ξ = 1) :
    glyzFourierProjector χ f = f := by
  ext x
  rw [glyzFourierProjector_apply_apply, glyz_schwartz_reproducing f χ hχ]

theorem fourier_glyzFourierProjector (χ f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (glyzFourierProjector χ f : E → ℂ) ξ = 𝓕 (f : E → ℂ) ξ * χ ξ := by
  rw [← SchwartzMap.fourier_coe, glyzFourierProjector_apply,
    SchwartzMap.fourier_convolution]
  change 𝓕 f ξ * 𝓕 (𝓕⁻ χ) ξ = _
  rw [fourier_fourierInv_eq]
  rfl

theorem support_fourier_glyzFourierProjector (χ f : SchwartzMap E ℂ) :
    Function.support (𝓕 (glyzFourierProjector χ f : E → ℂ)) ⊆ Function.support χ := by
  intro ξ hξ
  rw [Function.mem_support, fourier_glyzFourierProjector] at hξ
  exact (mul_ne_zero_iff.mp hξ).2

theorem glyzFourierProjector_norm_le (χ f : SchwartzMap E ℂ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hM : (∫ x, ‖glyzReproducingKernel χ x‖) ≤ M)
    (hf : ∀ x, ‖f x‖ ≤ B) (x : E) :
    ‖glyzFourierProjector χ f x‖ ≤ M * B := by
  rw [glyzFourierProjector_apply_apply, convolution_eq_swap]
  apply (norm_integral_le_of_norm_le
    ((glyzReproducingKernel χ).integrable.norm.const_mul B) ?_).trans
  · rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hM hB).trans_eq (mul_comm _ _)
  · exact Filter.Eventually.of_forall fun y => by
      simp only [ContinuousLinearMap.mul_apply', norm_mul]
      exact mul_le_mul_of_nonneg_right (hf (x - y)) (norm_nonneg _)

theorem glyzFourierProjector_power_integral_le (χ f : SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : (∫ x, ‖glyzReproducingKernel χ x‖) ≤ M) :
    (∫⁻ x, ‖glyzFourierProjector χ f x‖ₑ ^ (p : ℝ)) ≤
      ENNReal.ofReal M ^ (p : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) := by
  let K := glyzReproducingKernel χ
  let c : ℝ≥0∞ := ∫⁻ y, ‖K y‖ₑ
  have hc : c ≠ ⊤ := K.integrable.hasFiniteIntegral.ne
  have hcM : c ≤ ENNReal.ofReal M := by
    change (∫⁻ y, ‖K y‖ₑ) ≤ ENNReal.ofReal M
    rw [← ofReal_integral_norm_eq_lintegral_enorm K.integrable]
    exact ENNReal.ofReal_le_ofReal hM
  have hp1 : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr (show (1 : ℝ) ≤ p from hp)
  have hswap : (∫⁻ x, ∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ‖K y‖ₑ) =
      c * ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) := by
    rw [lintegral_lintegral_swap]
    · have hi (y : E) : (∫⁻ x, ‖f (x - y)‖ₑ ^ (p : ℝ) * ‖K y‖ₑ) =
          (∫⁻ x, ‖f x‖ₑ ^ (p : ℝ)) * ‖K y‖ₑ := by
        rw [lintegral_mul_const' (‖K y‖ₑ) _ (by finiteness),
          lintegral_sub_right_eq_self (fun x : E => ‖f x‖ₑ ^ (p : ℝ))]
      simp_rw [hi]
      rw [lintegral_const_mul'' _ K.continuous.measurable.enorm.aemeasurable]
      exact mul_comm _ _
    · exact (((f.continuous.measurable.comp (measurable_fst.sub measurable_snd)).enorm.pow_const _).mul
        (K.continuous.measurable.comp measurable_snd).enorm).aemeasurable
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ ^ (p : ℝ) * ‖K y‖ₑ) * c ^ ((p : ℝ) - 1) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [glyzFourierProjector_apply_apply]
      exact glyz_pointwise_kernel_holder f K hp x
    _ = (c * ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ)) * c ^ ((p : ℝ) - 1) := by
      rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hp1 hc), hswap]
    _ = (c * c ^ ((p : ℝ) - 1)) * ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) := by ring
    _ ≤ (ENNReal.ofReal M * ENNReal.ofReal M ^ ((p : ℝ) - 1)) *
        ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) :=
      mul_le_mul' (mul_le_mul' hcM (ENNReal.rpow_le_rpow hcM hp1)) le_rfl
    _ = _ := by
      have hh := ENNReal.rpow_add_of_nonneg (x := ENNReal.ofReal M)
        1 ((p : ℝ) - 1) (by norm_num) hp1
      rw [ENNReal.rpow_one, show 1 + ((p : ℝ) - 1) = p by ring] at hh
      rw [← hh]

theorem glyzFourierProjector_real_power_integral_le (χ f : SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : (∫ x, ‖glyzReproducingKernel χ x‖) ≤ M) :
    (∫⁻ x, ENNReal.ofReal (‖glyzFourierProjector χ f x‖ ^ (p : ℝ))) ≤
      ENNReal.ofReal (M ^ (p : ℝ)) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (p : ℝ)) := by
  simpa only [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) p.coe_nonneg,
    ENNReal.ofReal_rpow_of_nonneg hM0 p.coe_nonneg] using
      glyzFourierProjector_power_integral_le χ f hp hM0 hM

def glyzProjectionSum {ι : Type*} [Fintype ι] (χ : ι → SchwartzMap E ℂ) :
    (ι → SchwartzMap E ℂ) →ₗ[ℂ] SchwartzMap E ℂ :=
  ∑ i, (glyzFourierProjector (χ i)).comp (LinearMap.proj i)

@[simp] theorem glyzProjectionSum_apply {ι : Type*} [Fintype ι]
    (χ : ι → SchwartzMap E ℂ) (f : ι → SchwartzMap E ℂ) :
    glyzProjectionSum χ f = ∑ i, glyzFourierProjector (χ i) (f i) := by
  simp [glyzProjectionSum]

theorem glyzProjectionSum_norm_le {ι : Type*} [Fintype ι]
    (χ : ι → SchwartzMap E ℂ) {M B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i, (∫ x, ‖glyzReproducingKernel (χ i) x‖) ≤ M)
    (f : ι → SchwartzMap E ℂ) (hf : ∀ i x, ‖f i x‖ ≤ B) (x : E) :
    ‖glyzProjectionSum χ f x‖ ≤ ((Fintype.card ι : ℝ) * M) * B := by
  rw [glyzProjectionSum_apply, sum_apply]
  calc
    _ ≤ ∑ i, ‖glyzFourierProjector (χ i) (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, M * B :=
      Finset.sum_le_sum fun i _ => glyzFourierProjector_norm_le (χ i) (f i) hB (hM i) (hf i) x
    _ = _ := by simp; ring

theorem support_glyzAffineCutoff_subset_box {m : ℕ}
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) (a : GlyzSpace m)
    (R : ℝ) (hR : 0 < R) :
    Function.support (glyzAffineCutoff L a R hR) ⊆ glyzFrequencyBox L a (R + 1) := by
  intro ξ hξ
  have hnorm : ‖L.symm (ξ - a)‖ < R + 1 := by
    by_contra hh
    apply hξ
    have hz := (glyzBaseBump (E := GlyzSpace m) R hR).zero_of_le_dist
      (x := L.symm (ξ - a)) (by
        simpa only [glyzBaseBump, dist_zero_right] using le_of_not_gt hh)
    change ((((glyzBaseBump (E := GlyzSpace m) R hR) :
      GlyzSpace m → ℝ) (L.symm (ξ - a)) : ℝ) : ℂ) = 0
    rw [hz, Complex.ofReal_zero]
  change ‖(EuclideanSpace.equiv (Fin m) ℝ) (L.symm (ξ - a))‖ ≤ R + 1
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R + 1)).mpr
  intro i
  exact (PiLp.norm_apply_le (L.symm (ξ - a)) i).trans hnorm.le

end PlanarNikodym
