import PlanarNikodym.Analysis.Fourier.FrequencyRegularity

/-! Smoothness of actual Schwartz convolution for integrable inputs.
Every derivative is obtained by differentiating the Schwartz kernel under
the integral, with its bounded derivative providing an integrable majorant. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Convolution

namespace PlanarNikodym

/-- Differentiation of the actual convolution with a Schwartz kernel.
The bilinear formulation also applies to operator-valued kernel derivatives. -/
theorem hasFDerivAt_convolution_schwartz
    {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : ℂ →L[ℝ] F →L[ℝ] G) {f : Plane → ℂ} (hf : Integrable f)
    (K : SchwartzMap Plane F) (x₀ : Plane) :
    HasFDerivAt (f ⋆[L] K)
      ((f ⋆[L.precompR Plane] (SchwartzMap.fderivCLM ℝ Plane F K)) x₀) x₀ := by
  let KD : SchwartzMap Plane (Plane →L[ℝ] F) := SchwartzMap.fderivCLM ℝ Plane F K
  let LD := L.precompR Plane
  letI := ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := ℂ)
    (F := (Plane →L[ℝ] F) →L[ℝ] Plane →L[ℝ] G) (σ₁₂ := RingHom.id ℝ)
  let C₀ : ℝ := SchwartzMap.seminorm ℝ 0 0 K
  let C₁ : ℝ := SchwartzMap.seminorm ℝ 0 0 KD
  have hK (x : Plane) : ‖K x‖ ≤ C₀ := K.norm_le_seminorm ℝ x
  have hKD (x : Plane) : ‖KD x‖ ≤ C₁ := KD.norm_le_seminorm ℝ x
  have hFmeas (x : Plane) :
      AEStronglyMeasurable (fun y => L (f y) (K (x - y))) volume :=
    hf.aestronglyMeasurable.convolution_integrand_snd L K.continuous.aestronglyMeasurable x
  have hFint (x : Plane) : Integrable (fun y => L (f y) (K (x - y))) := by
    apply ((hf.norm.const_mul ‖L‖).mul_const C₀).mono' (hFmeas x)
    exact ae_of_all _ (fun y => (L.le_opNorm₂ (f y) (K (x - y))).trans (by
      gcongr
      exact hK (x - y)))
  have hDmeas (x : Plane) :
      AEStronglyMeasurable (fun y => LD (f y) (KD (x - y))) volume :=
    hf.aestronglyMeasurable.convolution_integrand_snd LD KD.continuous.aestronglyMeasurable x
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

/-- Convolution with a Schwartz kernel is continuously differentiable to
every finite order, even when the original input is only integrable. -/
theorem contDiff_nat_convolution_schwartz (n : ℕ)
    {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : ℂ →L[ℝ] F →L[ℝ] G) {f : Plane → ℂ} (hf : Integrable f)
    (K : SchwartzMap Plane F) : ContDiff ℝ n (f ⋆[L] K) := by
  induction n generalizing F G with
  | zero =>
    apply contDiff_zero.mpr
    have hbb : BddAbove (range (fun x => ‖K x‖)) := by
      refine ⟨SchwartzMap.seminorm ℝ 0 0 K, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact K.norm_le_seminorm ℝ x
    exact hbb.continuous_convolution_right_of_integrable L hf K.continuous
  | succ n ih =>
    exact contDiff_succ_iff_hasFDerivAt.mpr
      ⟨f ⋆[L.precompR Plane] (SchwartzMap.fderivCLM ℝ Plane F K),
        ih (L.precompR Plane) (SchwartzMap.fderivCLM ℝ Plane F K),
        hasFDerivAt_convolution_schwartz L hf K⟩

/-- Actual Schwartz convolution is `C∞`; no compact support of the physical
kernel and no differentiability of the input are assumed. -/
theorem contDiff_infty_convolution_schwartz
    {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : ℂ →L[ℝ] F →L[ℝ] G) {f : Plane → ℂ} (hf : Integrable f)
    (K : SchwartzMap Plane F) : ContDiff ℝ ∞ (f ⋆[L] K) :=
  contDiff_infty.mpr (fun n => contDiff_nat_convolution_schwartz n L hf K)

theorem contDiff_infty_integral_schwartz_mul {f : Plane → ℂ} (hf : Integrable f)
    (K : SchwartzMap Plane ℂ) :
    ContDiff ℝ ∞ (fun x => ∫ y, K (x - y) * f y) := by
  have heq : (fun x => ∫ y, K (x - y) * f y) =
      f ⋆[ContinuousLinearMap.mul ℝ ℂ] K := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    exact ae_of_all _ (fun y => mul_comm _ _)
  rw [heq]
  exact contDiff_infty_convolution_schwartz (ContinuousLinearMap.mul ℝ ℂ) hf K

theorem FrequencyCutoff.band_contDiff_infty (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) : ContDiff ℝ ∞ (L.band k f) := by
  let K := inverseFourierSchwartz (L.bandSymbol k)
    (L.bandSymbol_smooth k) (L.bandSymbol_compact k)
  change ContDiff ℝ ∞ (fun x => ∫ y, L.bandKernel k (x - y) * f y)
  simpa only [K, inverseFourierSchwartz_coe, FrequencyCutoff.bandKernel,
    FrequencyCutoff.band] using contDiff_infty_integral_schwartz_mul hf K

theorem FrequencyCutoff.low_contDiff_infty (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) : ContDiff ℝ ∞ (L.low f) := by
  let K := inverseFourierSchwartz (L.lowSymbol 0)
    (L.lowSymbol_smooth 0) (L.lowSymbol_compact 0)
  change ContDiff ℝ ∞ (fun x => ∫ y, L.lowKernel (x - y) * f y)
  simpa only [K, inverseFourierSchwartz_coe, FrequencyCutoff.lowKernel,
    FrequencyCutoff.low] using contDiff_infty_integral_schwartz_mul hf K

end PlanarNikodym
