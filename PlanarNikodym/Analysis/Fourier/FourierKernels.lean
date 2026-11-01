import PlanarNikodym.Analysis.Fourier.FrequencyLocalization
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Convolution

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal NNReal

namespace PlanarNikodym

/-- Euclidean coordinates used only to invoke the Schwartz Fourier transform.
The original `Plane` keeps its product norm. -/
abbrev FourierPlane := WithLp 2 Plane

def fourierPlaneEquiv : FourierPlane ≃L[ℝ] Plane :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ

theorem inverseFourierIntegral_eq_euclidean (m : Plane → ℝ) (x : Plane) :
    inverseFourierIntegral m x =
      𝓕⁻ (fun ξ : FourierPlane => (m (WithLp.ofLp ξ) : ℂ)) (WithLp.toLp 2 x) := by
  rw [Real.fourierInv_eq']
  unfold inverseFourierIntegral
  rw [← (WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 Plane).symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply,
    conj_trivial, smul_eq_mul, fourierPhase]
  rw [mul_comm (m _ : ℂ)]

/-- The actual inverse integral of a smooth compactly supported symbol,
packaged as a Schwartz function on the original product-norm plane. -/
def inverseFourierSchwartz (m : Plane → ℝ) (hm : ContDiff ℝ ∞ m)
    (hc : HasCompactSupport m) : SchwartzMap Plane ℂ := by
  let f : SchwartzMap Plane ℂ :=
    (hc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hm)
  let fE : SchwartzMap FourierPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv f
  exact SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv.symm (𝓕⁻ fE)

@[simp] theorem inverseFourierSchwartz_apply (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) (x : Plane) :
    inverseFourierSchwartz m hm hc x = inverseFourierIntegral m x := by
  rw [inverseFourierIntegral_eq_euclidean]
  exact congrFun (SchwartzMap.fourierInv_coe _) (fourierPlaneEquiv.symm x)

theorem inverseFourierSchwartz_coe (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) :
    ⇑(inverseFourierSchwartz m hm hc) = inverseFourierIntegral m := by
  funext x
  exact inverseFourierSchwartz_apply m hm hc x

theorem inverseFourierIntegral_integrable (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) :
    Integrable (inverseFourierIntegral m) := by
  simpa only [inverseFourierSchwartz_coe] using
    (inverseFourierSchwartz m hm hc).integrable (μ := volume)

theorem inverseFourierIntegral_smooth (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) :
    ContDiff ℝ ∞ (inverseFourierIntegral m) := by
  simpa only [inverseFourierSchwartz_coe] using
    (inverseFourierSchwartz m hm hc).smooth ⊤

theorem inverseFourierIntegral_rapid_decay (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ^ n * ‖inverseFourierIntegral m x‖ ≤ C := by
  simpa only [inverseFourierSchwartz_apply, norm_iteratedFDeriv_zero] using
    (inverseFourierSchwartz m hm hc).decay n 0

theorem inverseFourierIntegral_weighted_integrable (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) (n : ℕ) :
    Integrable (fun x => ‖x‖ ^ n * ‖inverseFourierIntegral m x‖) := by
  simpa only [inverseFourierSchwartz_apply] using
    (inverseFourierSchwartz m hm hc).integrable_pow_mul volume n

theorem inverseFourierIntegral_dilate (m : Plane → ℝ) {a : ℝ}
    (ha : 0 < a) (x : Plane) :
    inverseFourierIntegral (fun ξ => m (a⁻¹ • ξ)) x =
      (a ^ 2 : ℝ) • inverseFourierIntegral m (a • x) := by
  have hd : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
  have hi := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Plane)
    (f := fun ξ => (m ξ : ℂ) * Complex.exp
      (((2 * Real.pi * fourierPhase (a • x) ξ : ℝ) : ℂ) * Complex.I)) ha.le
  rw [hd] at hi
  unfold inverseFourierIntegral
  rw [← hi]
  congr 1
  funext ξ
  congr 2
  congr 1
  simp only [fourierPhase, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  field_simp [ha.ne']

theorem FrequencyCutoff.lowSymbol_smooth (L : FrequencyCutoff) (N : ℕ) :
    ContDiff ℝ ∞ (L.lowSymbol N) := by
  unfold lowSymbol
  have hφ := L.smooth
  fun_prop

theorem FrequencyCutoff.lowKernel_integrable (L : FrequencyCutoff) :
    Integrable L.lowKernel :=
  inverseFourierIntegral_integrable _ (L.lowSymbol_smooth 0) (L.lowSymbol_compact 0)

theorem FrequencyCutoff.bandKernel_integrable (L : FrequencyCutoff) (k : ℕ) :
    Integrable (L.bandKernel k) :=
  inverseFourierIntegral_integrable _ (L.bandSymbol_smooth k) (L.bandSymbol_compact k)

theorem FrequencyCutoff.lowKernel_smooth (L : FrequencyCutoff) :
    ContDiff ℝ ∞ L.lowKernel :=
  inverseFourierIntegral_smooth _ (L.lowSymbol_smooth 0) (L.lowSymbol_compact 0)

theorem FrequencyCutoff.bandKernel_smooth (L : FrequencyCutoff) (k : ℕ) :
    ContDiff ℝ ∞ (L.bandKernel k) :=
  inverseFourierIntegral_smooth _ (L.bandSymbol_smooth k) (L.bandSymbol_compact k)

theorem FrequencyCutoff.lowKernel_rapid_decay (L : FrequencyCutoff) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ^ n * ‖L.lowKernel x‖ ≤ C :=
  inverseFourierIntegral_rapid_decay _ (L.lowSymbol_smooth 0) (L.lowSymbol_compact 0) n

theorem FrequencyCutoff.bandKernel_rapid_decay (L : FrequencyCutoff) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ^ n * ‖L.bandKernel k x‖ ≤ C :=
  inverseFourierIntegral_rapid_decay _ (L.bandSymbol_smooth k) (L.bandSymbol_compact k) n

theorem FrequencyCutoff.lowSymbol_kernel_scaling (L : FrequencyCutoff) (N : ℕ)
    (x : Plane) :
    inverseFourierIntegral (L.lowSymbol N) x =
      ((2 : ℝ) ^ N) ^ 2 • L.lowKernel ((2 : ℝ) ^ N • x) := by
  change inverseFourierIntegral (fun ξ => L.symbol (((2 : ℝ) ^ N)⁻¹ • ξ)) x =
    ((2 : ℝ) ^ N) ^ 2 • inverseFourierIntegral (L.lowSymbol 0) ((2 : ℝ) ^ N • x)
  rw [show L.lowSymbol 0 = L.symbol by funext ξ; exact L.lowSymbol_zero ξ]
  exact inverseFourierIntegral_dilate L.symbol
    (pow_pos (by norm_num : (0 : ℝ) < 2) N) x

theorem inverseFourierIntegral_memLp (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) (p : ℝ≥0∞) :
    MemLp (inverseFourierIntegral m) p volume := by
  simpa only [inverseFourierSchwartz_coe] using
    (inverseFourierSchwartz m hm hc).memLp p volume

theorem FrequencyCutoff.lowKernel_memLp (L : FrequencyCutoff) (p : ℝ≥0∞) :
    MemLp L.lowKernel p volume :=
  inverseFourierIntegral_memLp _ (L.lowSymbol_smooth 0) (L.lowSymbol_compact 0) p

theorem FrequencyCutoff.bandKernel_memLp (L : FrequencyCutoff) (k : ℕ) (p : ℝ≥0∞) :
    MemLp (L.bandKernel k) p volume :=
  inverseFourierIntegral_memLp _ (L.bandSymbol_smooth k) (L.bandSymbol_compact k) p

/-- Pointwise Hölder bound for the actual low-frequency convolution. -/
theorem FrequencyCutoff.low_enorm_le (L : FrequencyCutoff) {p q : ℝ≥0∞}
    [ENNReal.HolderConjugate q p] {f : Plane → ℂ}
    (hf : AEStronglyMeasurable f volume) (x : Plane) :
    ‖L.low f x‖ₑ ≤ eLpNorm L.lowKernel q volume * eLpNorm f p volume := by
  let K : Plane → ℂ := fun y => L.lowKernel (x - y)
  have hK : MemLp K q volume :=
    (L.lowKernel_memLp q).comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  calc
    _ ≤ ∫⁻ y, ‖K y * f y‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (K • f) 1 volume := by
      simp only [eLpNorm_one_eq_lintegral_enorm, smul_eq_mul, Pi.mul_apply]
    _ ≤ eLpNorm K q volume * eLpNorm f p volume :=
      eLpNorm_smul_le_mul_eLpNorm hf hK.aestronglyMeasurable
    _ = _ := by
      congr 1
      exact eLpNorm_comp_measurePreserving (L.lowKernel_memLp q).aestronglyMeasurable
        (Measure.measurePreserving_sub_left volume x)

theorem FrequencyCutoff.low_integrand_integrable (L : FrequencyCutoff) {p q : ℝ≥0∞}
    [ENNReal.HolderConjugate q p] {f : Plane → ℂ} (hf : MemLp f p volume)
    (x : Plane) : Integrable (fun y => L.lowKernel (x - y) * f y) := by
  have hK := (L.lowKernel_memLp q).comp_measurePreserving
    (Measure.measurePreserving_sub_left volume x)
  exact (memLp_one_iff_integrable.mp (hf.smul hK))

theorem FrequencyCutoff.band_integrand_integrable (L : FrequencyCutoff) (k : ℕ)
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate q p] {f : Plane → ℂ}
    (hf : MemLp f p volume) (x : Plane) :
    Integrable (fun y => L.bandKernel k (x - y) * f y) := by
  have hK := (L.bandKernel_memLp k q).comp_measurePreserving
    (Measure.measurePreserving_sub_left volume x)
  exact (memLp_one_iff_integrable.mp (hf.smul hK))

end PlanarNikodym
