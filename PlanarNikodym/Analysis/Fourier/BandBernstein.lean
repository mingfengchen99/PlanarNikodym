import PlanarNikodym.Analysis.Fourier.DyadicKernelJets
import PlanarNikodym.Analysis.Fourier.LpKernelConvolution
import PlanarNikodym.Analysis.Maximal.DyadicSummation

/-! Bernstein bounds for the actual frequency localization. These control
the full spatial derivatives of `L.band k f` by the original input's Lp norm.
The constants depend on the cutoff and derivative order, uniformly in `p`, `k`, and `f`. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution NNReal ENNReal

namespace PlanarNikodym

theorem dyadicWeight_nat_eq (j k : ℕ) :
    dyadicWeight (j : ℝ) k = ENNReal.ofReal (((2 : ℝ) ^ k) ^ j) := by
  simp only [dyadicWeight, Real.rpow_natCast]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Young's inequality applied to the exact full-jet convolution formula. -/
theorem FrequencyCutoff.eLpNorm_iteratedFDeriv_band_le_kernel (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) {p : ℝ≥0} (hp : 1 ≤ p) (j k : ℕ) :
    eLpNorm (iteratedFDeriv ℝ j (L.band k f)) p volume ≤
      eLpNorm f p volume * ENNReal.ofReal
        (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel k) x‖) := by
  let K := inverseFourierSchwartz (L.bandSymbol k)
    (L.bandSymbol_smooth k) (L.bandSymbol_compact k)
  let J := schwartzJet j K
  have hfun : iteratedFDeriv ℝ j (L.band k f) =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℂ] J := by
    funext x
    rw [L.iteratedFDeriv_band_eq_integral hf j k x]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, J, schwartzJet_apply,
      K, inverseFourierSchwartz_coe, FrequencyCutoff.bandKernel]
  have hkernel : eLpNorm J 1 volume = ENNReal.ofReal
      (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel k) x‖) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (J.integrable (μ := volume))]
    simp only [J, schwartzJet_apply, K, inverseFourierSchwartz_coe, FrequencyCutoff.bandKernel]
  rw [hfun, ← hkernel]
  exact eLpNorm_convolution_schwartz_smul_le hf J hp

/-- All finite exponents `p ≥ 1`, including `p = 1`, with the exact fixed
kernel L1 coefficient and one frequency factor per full spatial derivative. -/
theorem FrequencyCutoff.eLpNorm_iteratedFDeriv_band_le (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) {p : ℝ≥0} (hp : 1 ≤ p) (j k : ℕ) :
    eLpNorm (iteratedFDeriv ℝ j (L.band k f)) p volume ≤
      ENNReal.ofReal (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) *
        dyadicWeight (j : ℝ) k * eLpNorm f p volume := by
  apply (L.eLpNorm_iteratedFDeriv_band_le_kernel hf hp j k).trans_eq
  rw [L.integral_norm_bandKernel_iteratedFDeriv,
    ENNReal.ofReal_mul (by positivity), ← dyadicWeight_nat_eq]
  ac_rfl

theorem FrequencyCutoff.memLp_iteratedFDeriv_band (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) {p : ℝ≥0} (hp : 1 ≤ p)
    (hfp : MemLp f p volume) (j k : ℕ) :
    MemLp (iteratedFDeriv ℝ j (L.band k f)) p volume := by
  refine ⟨(contDiff_infty.mp (L.band_contDiff_infty k hf) j).continuous_iteratedFDeriv'.aestronglyMeasurable,
    (L.eLpNorm_iteratedFDeriv_band_le_kernel hf hp j k).trans_lt ?_⟩
  exact ENNReal.mul_lt_top hfp.eLpNorm_lt_top ENNReal.ofReal_lt_top

/-- The normalization used in the jet estimates cancels the full spatial
derivative's frequency cost. This concerns the input band before averaging. -/
theorem FrequencyCutoff.scaled_eLpNorm_iteratedFDeriv_band_le (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) {p : ℝ≥0} (hp : 1 ≤ p) (j k : ℕ) :
    dyadicWeight (-(j : ℝ)) k * eLpNorm (iteratedFDeriv ℝ j (L.band k f)) p volume ≤
      ENNReal.ofReal (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) *
        eLpNorm f p volume := by
  calc
    _ ≤ dyadicWeight (-(j : ℝ)) k *
        (ENNReal.ofReal (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) *
          dyadicWeight (j : ℝ) k * eLpNorm f p volume) :=
      mul_le_mul_right (L.eLpNorm_iteratedFDeriv_band_le hf hp j k) _
    _ = ENNReal.ofReal (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) *
        (dyadicWeight (-(j : ℝ)) k * dyadicWeight (j : ℝ) k) * eLpNorm f p volume := by ac_rfl
    _ = _ := by rw [← dyadicWeight_add]; simp [dyadicWeight]

/-- Every finite normalized spatial-jet sum has a constant independent of
the frequency, exponent and input. No curve-average smoothing gain is asserted. -/
theorem FrequencyCutoff.scaled_band_jet_sum_le (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Integrable f) {p : ℝ≥0} (hp : 1 ≤ p) (s k : ℕ) :
    (∑ j ∈ Finset.range (s + 1), dyadicWeight (-(j : ℝ)) k *
      eLpNorm (iteratedFDeriv ℝ j (L.band k f)) p volume) ≤
      (∑ j ∈ Finset.range (s + 1), ENNReal.ofReal
        (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖)) * eLpNorm f p volume := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _ => L.scaled_eLpNorm_iteratedFDeriv_band_le hf hp j k)

/-- A positive constant chosen once for the cutoff and derivative order.
The same constant works for every finite exponent at least one. -/
theorem FrequencyCutoff.exists_uniform_band_jet_Lp_bound (L : FrequencyCutoff) (j : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (p : ℝ≥0), 1 ≤ p → ∀ (k : ℕ) (f : Plane → ℂ),
      Integrable f → eLpNorm (iteratedFDeriv ℝ j (L.band k f)) p volume ≤
        (C : ℝ≥0∞) * dyadicWeight (j : ℝ) k * eLpNorm f p volume := by
  have hI : 0 ≤ ∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  let C : ℝ≥0 := ⟨(∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) + 1,
    by linarith⟩
  have hC : (0 : ℝ) < C := by
    change 0 < (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) + 1
    linarith
  refine ⟨C, by exact_mod_cast hC, ?_⟩
  intro p hp k f hf
  apply (L.eLpNorm_iteratedFDeriv_band_le hf hp j k).trans
  gcongr
  have h : (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) ≤ (C : ℝ) := by
    change (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) ≤
      (∫ x : Plane, ‖iteratedFDeriv ℝ j (L.bandKernel 0) x‖) + 1
    linarith
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal h

end PlanarNikodym
