import PlanarNikodym.Analysis.Fourier.FourierKernels

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal NNReal Convolution

namespace PlanarNikodym

/-- Fourier inversion at the origin gives the mass of the actual kernel. -/
theorem integral_inverseFourierIntegral (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) :
    ∫ x, inverseFourierIntegral m x = (m 0 : ℂ) := by
  let f : SchwartzMap Plane ℂ :=
    (hc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hm)
  let fE : SchwartzMap FourierPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv f
  have hi : (∫ ξ : FourierPlane, (𝓕⁻ fE) ξ) = fE 0 := by
    have h := congrArg (fun g : SchwartzMap FourierPlane ℂ => g 0)
      (FourierTransform.fourier_fourierInv_eq (F := SchwartzMap FourierPlane ℂ) fE)
    rw [SchwartzMap.fourier_coe, Real.fourier_eq] at h
    simpa using h
  calc
    _ = ∫ ξ : FourierPlane, inverseFourierIntegral m (WithLp.ofLp ξ) :=
      ((WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 Plane).symm.measurableEmbedding _).symm
    _ = ∫ ξ : FourierPlane, (𝓕⁻ fE) ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [inverseFourierIntegral_eq_euclidean]
      exact (congrFun (SchwartzMap.fourierInv_coe fE) ξ).symm
    _ = _ := hi

@[simp] theorem FrequencyCutoff.integral_lowKernel (L : FrequencyCutoff) :
    ∫ x, L.lowKernel x = (1 : ℂ) := by
  rw [FrequencyCutoff.lowKernel,
    integral_inverseFourierIntegral _ (L.lowSymbol_smooth 0) (L.lowSymbol_compact 0)]
  rw [L.lowSymbol_zero, L.near_zero 0 (by simp), Complex.ofReal_one]

@[simp] theorem FrequencyCutoff.integral_bandKernel (L : FrequencyCutoff) (k : ℕ) :
    ∫ x, L.bandKernel k x = (0 : ℂ) := by
  rw [FrequencyCutoff.bandKernel,
    integral_inverseFourierIntegral _ (L.bandSymbol_smooth k) (L.bandSymbol_compact k)]
  rw [L.bandSymbol_vanishes_near_zero k (by simp : ‖(0 : Plane)‖ ≤ 1), Complex.ofReal_zero]

theorem FrequencyCutoff.bandSymbol_rescale (L : FrequencyCutoff) (k : ℕ) (ξ : Plane) :
    L.bandSymbol k ξ = L.bandSymbol 0 (((2 : ℝ) ^ k)⁻¹ • ξ) := by
  simp [FrequencyCutoff.bandSymbol, FrequencyCutoff.lowSymbol, pow_succ,
    smul_smul, mul_inv_rev]

theorem FrequencyCutoff.bandKernel_scaling (L : FrequencyCutoff) (k : ℕ) (x : Plane) :
    L.bandKernel k x = ((2 : ℝ) ^ k) ^ 2 • L.bandKernel 0 ((2 : ℝ) ^ k • x) := by
  unfold FrequencyCutoff.bandKernel
  rw [show L.bandSymbol k = (fun ξ => L.bandSymbol 0 (((2 : ℝ) ^ k)⁻¹ • ξ)) by
    funext ξ; exact L.bandSymbol_rescale k ξ]
  exact inverseFourierIntegral_dilate _ (pow_pos (by norm_num : (0 : ℝ) < 2) k) x

theorem FrequencyCutoff.low_eq_convolution (L : FrequencyCutoff) (f : Plane → ℂ) :
    L.low f = f ⋆[ContinuousLinearMap.mul ℂ ℂ] L.lowKernel := by
  funext x
  simp only [FrequencyCutoff.low, convolution_def, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  filter_upwards [] with y
  exact mul_comm _ _

theorem FrequencyCutoff.low_integrable (L : FrequencyCutoff) {f : Plane → ℂ}
    (hf : Integrable f) : Integrable (L.low f) := by
  rw [L.low_eq_convolution]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) L.lowKernel_integrable

theorem FrequencyCutoff.low_continuous (L : FrequencyCutoff) {f : Plane → ℂ}
    (hf : Integrable f) : Continuous (L.low f) := by
  obtain ⟨C, _, hC⟩ := L.lowKernel_rapid_decay 0
  have hb : BddAbove (range (fun x => ‖L.lowKernel x‖)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa using hC x
  rw [L.low_eq_convolution]
  exact hb.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hf L.lowKernel_smooth.continuous

end PlanarNikodym
