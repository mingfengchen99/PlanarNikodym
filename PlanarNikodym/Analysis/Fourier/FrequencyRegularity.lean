import PlanarNikodym.Analysis.Fourier.FourierKernels
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Regularity of the actual frequency-localization operators for `L¹`
inputs.  A Schwartz kernel need not have compact support, so differentiation
under the convolution integral uses its globally bounded first derivative. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Convolution

namespace PlanarNikodym

/-- Convolution of an `L¹` function with an actual Schwartz kernel is `C¹`.
The derivative is the convolution with the actual derivative of the kernel. -/
theorem contDiff_one_convolution_schwartz {f : Plane → ℂ} (hf : Integrable f)
    (K : SchwartzMap Plane ℂ) :
    ContDiff ℝ 1 (f ⋆[ContinuousLinearMap.mul ℝ ℂ] K) := by
  let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  let KD : SchwartzMap Plane (Plane →L[ℝ] ℂ) := SchwartzMap.fderivCLM ℝ Plane ℂ K
  let LD := L.precompR Plane
  letI := ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := ℂ)
    (F := (Plane →L[ℝ] ℂ) →L[ℝ] Plane →L[ℝ] ℂ) (σ₁₂ := RingHom.id ℝ)
  let C₀ : ℝ := SchwartzMap.seminorm ℝ 0 0 K
  let C₁ : ℝ := SchwartzMap.seminorm ℝ 0 0 KD
  have hK (x : Plane) : ‖K x‖ ≤ C₀ := K.norm_le_seminorm ℝ x
  have hKD (x : Plane) : ‖KD x‖ ≤ C₁ := KD.norm_le_seminorm ℝ x
  have hKDbb : BddAbove (range (fun x => ‖KD x‖)) := by
    refine ⟨C₁, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hKD x
  have hFmeas (x : Plane) :
      AEStronglyMeasurable (fun y => L (f y) (K (x - y))) volume :=
    hf.aestronglyMeasurable.convolution_integrand_snd L K.continuous.aestronglyMeasurable x
  have hFint (x : Plane) : Integrable (fun y => L (f y) (K (x - y))) := by
    apply (((hf.norm.const_mul ‖L‖).mul_const C₀)).mono' (hFmeas x)
    exact ae_of_all _ (fun y => (L.le_opNorm₂ (f y) (K (x - y))).trans (by
      gcongr
      exact hK (x - y)))
  have hDmeas (x : Plane) :
      AEStronglyMeasurable (fun y => LD (f y) (KD (x - y))) volume :=
    hf.aestronglyMeasurable.convolution_integrand_snd LD KD.continuous.aestronglyMeasurable x
  have hDcont : Continuous (f ⋆[LD] KD) :=
    hKDbb.continuous_convolution_right_of_integrable LD hf KD.continuous
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨f ⋆[LD] KD, hDcont, ?_⟩
  intro x₀
  change HasFDerivAt (fun x => ∫ y, L (f y) (K (x - y)))
    (∫ y, LD (f y) (KD (x₀ - y))) x₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x y => LD (f y) (KD (x - y))) (s := univ)
    (bound := fun y => ‖LD‖ * ‖f y‖ * C₁) Filter.univ_mem
    (Eventually.of_forall hFmeas) (hFint x₀) (hDmeas x₀)
  · exact ae_of_all _ (fun y x _ => (LD.le_opNorm₂ (f y) (KD (x - y))).trans (by
      gcongr
      exact hKD (x - y)))
  · exact (hf.norm.const_mul ‖LD‖).mul_const C₁
  · filter_upwards [] with y x _
    have hsub : HasFDerivAt (fun x : Plane => x - y)
        (ContinuousLinearMap.id ℝ Plane) x := (hasFDerivAt_id x).sub_const y
    have hkernel := (K.hasFDerivAt (x - y)).comp x hsub
    change HasFDerivAt (fun x => L (f y) (K (x - y)))
      ((L (f y)).comp (fderiv ℝ K (x - y))) x
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def]
      using (L (f y)).hasFDerivAt.comp x hkernel

/-- The actual convolution written in the project's kernel-first order. -/
theorem contDiff_one_integral_schwartz_mul {f : Plane → ℂ} (hf : Integrable f)
    (K : SchwartzMap Plane ℂ) :
    ContDiff ℝ 1 (fun x => ∫ y, K (x - y) * f y) := by
  have heq : (fun x => ∫ y, K (x - y) * f y) =
      f ⋆[ContinuousLinearMap.mul ℝ ℂ] K := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    exact ae_of_all _ (fun y => mul_comm _ _)
  rw [heq]
  exact contDiff_one_convolution_schwartz hf K

theorem FrequencyCutoff.band_contDiff_one (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) : ContDiff ℝ 1 (L.band k f) := by
  let K := inverseFourierSchwartz (L.bandSymbol k)
    (L.bandSymbol_smooth k) (L.bandSymbol_compact k)
  have h := contDiff_one_integral_schwartz_mul hf K
  change ContDiff ℝ 1 (fun x => ∫ y, L.bandKernel k (x - y) * f y)
  simpa only [K, inverseFourierSchwartz_coe, FrequencyCutoff.bandKernel,
    FrequencyCutoff.band] using h

theorem FrequencyCutoff.low_contDiff_one (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) : ContDiff ℝ 1 (L.low f) := by
  let K := inverseFourierSchwartz (L.lowSymbol 0)
    (L.lowSymbol_smooth 0) (L.lowSymbol_compact 0)
  have h := contDiff_one_integral_schwartz_mul hf K
  change ContDiff ℝ 1 (fun x => ∫ y, L.lowKernel (x - y) * f y)
  simpa only [K, inverseFourierSchwartz_coe, FrequencyCutoff.lowKernel,
    FrequencyCutoff.low] using h

end PlanarNikodym
