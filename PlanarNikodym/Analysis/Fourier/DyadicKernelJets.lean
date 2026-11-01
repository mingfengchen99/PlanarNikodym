import PlanarNikodym.Analysis.Fourier.SchwartzConvolutionSmooth
import PlanarNikodym.Analysis.Fourier.FourierKernelIdentities

/-! Exact high-order scaling of the actual dyadic convolution kernels.
Their derivative L1 cost is precisely `2^(j*k)` times a fixed constant. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

theorem FrequencyCutoff.bandKernel_iteratedFDeriv_scaling (L : FrequencyCutoff) (j k : ℕ)
    (x : Plane) :
    iteratedFDeriv ℝ j (L.bandKernel k) x =
      (((2 : ℝ) ^ k) ^ 2 * ((2 : ℝ) ^ k) ^ j) •
        iteratedFDeriv ℝ j (L.bandKernel 0) ((2 : ℝ) ^ k • x) := by
  have hf : ContDiff ℝ j (L.bandKernel 0) := contDiff_infty.mp (L.bandKernel_smooth 0) j
  have hg : ContDiff ℝ j (fun x : Plane => L.bandKernel 0 ((2 : ℝ) ^ k • x)) :=
    hf.comp ((contDiff_const (c := (2 : ℝ) ^ k)).smul contDiff_id)
  have heq : L.bandKernel k = fun x => ((2 : ℝ) ^ k) ^ 2 •
      L.bandKernel 0 ((2 : ℝ) ^ k • x) := funext (L.bandKernel_scaling k)
  rw [heq, iteratedFDeriv_const_smul_apply' hg.contDiffAt]
  rw [congrFun (iteratedFDeriv_comp_const_smul ((2 : ℝ) ^ k) hf) x, smul_smul]

theorem FrequencyCutoff.norm_bandKernel_iteratedFDeriv_scaling (L : FrequencyCutoff) (j k : ℕ)
    (x : Plane) :
    ‖iteratedFDeriv ℝ j (L.bandKernel k) x‖ =
      ((2 : ℝ) ^ k) ^ (j + 2) *
        ‖iteratedFDeriv ℝ j (L.bandKernel 0) ((2 : ℝ) ^ k • x)‖ := by
  rw [L.bandKernel_iteratedFDeriv_scaling, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), pow_add]
  ring

theorem FrequencyCutoff.integrable_norm_bandKernel_iteratedFDeriv (L : FrequencyCutoff) (j k : ℕ) :
    Integrable (fun x : Plane => ‖iteratedFDeriv ℝ j (L.bandKernel k) x‖) := by
  let K := inverseFourierSchwartz (L.bandSymbol k)
    (L.bandSymbol_smooth k) (L.bandSymbol_compact k)
  simpa only [pow_zero, one_mul, K, inverseFourierSchwartz_coe, FrequencyCutoff.bandKernel] using
    K.integrable_pow_mul_iteratedFDeriv volume 0 j

/-- Exact L1 scaling, with the spatial Jacobian cancelling the kernel's
dimension-two normalization. The remaining cost is one frequency per derivative. -/
theorem FrequencyCutoff.integral_norm_bandKernel_iteratedFDeriv (L : FrequencyCutoff) (j k : ℕ) :
    (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel k) x‖) =
      ((2 : ℝ) ^ k) ^ j * ∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖ := by
  simp_rw [L.norm_bandKernel_iteratedFDeriv_scaling j k]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg (volume : Measure Plane)
      (fun x => ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) ((2 : ℝ) ^ k)
      (hR := by positivity)]
  simp only [Plane, Module.finrank_prod, Module.finrank_self, Nat.reduceAdd, smul_eq_mul, pow_add]
  field_simp

theorem FrequencyCutoff.exists_uniform_bandKernel_jet_L1_bound (L : FrequencyCutoff) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel k) x‖) ≤ C * ((2 : ℝ) ^ k) ^ j := by
  let C : ℝ := (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro k
  rw [L.integral_norm_bandKernel_iteratedFDeriv]
  dsimp [C]
  nlinarith [show 0 < ((2 : ℝ) ^ k) ^ j by positivity]

end PlanarNikodym
