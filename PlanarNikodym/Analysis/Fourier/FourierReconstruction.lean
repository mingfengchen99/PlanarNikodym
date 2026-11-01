import PlanarNikodym.Analysis.Fourier.FourierKernelIdentities
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Pointwise reconstruction by the actual dyadic Fourier kernels. The
kernel may be complex valued. The argument uses its mass and integrability,
rather than positivity or a Fourier transform of the test function. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff FourierTransform ENNReal NNReal Convolution
namespace PlanarNikodym

/-- Actual convolution with the low symbol at scale `2^N`. -/
def FrequencyCutoff.lowAtScale (L : FrequencyCutoff) (N : ℕ)
    (f : Plane → ℂ) (x : Plane) : ℂ :=
  ∫ y, inverseFourierIntegral (L.lowSymbol N) (x - y) * f y

@[simp] theorem FrequencyCutoff.lowAtScale_zero (L : FrequencyCutoff) (f : Plane → ℂ) :
    L.lowAtScale 0 f = L.low f := rfl

theorem FrequencyCutoff.lowAtScale_eq_rescaled (L : FrequencyCutoff) (N : ℕ)
    (f : Plane → ℂ) (x : Plane) :
    L.lowAtScale N f x =
      ∫ y, L.lowKernel y * f (x - ((2 : ℝ) ^ N)⁻¹ • y) := by
  let a : ℝ := (2 : ℝ) ^ N
  have ha : 0 < a := pow_pos (by norm_num) N
  have hd : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
  let H : Plane → ℂ := fun y => L.lowKernel y * f (x - a⁻¹ • y)
  calc
    _ = ∫ y, inverseFourierIntegral (L.lowSymbol N) y * f (x - y) := by
      have h := integral_sub_left_eq_self
        (fun y => inverseFourierIntegral (L.lowSymbol N) (x - y) * f y)
        (volume : Measure Plane) x
      simpa only [lowAtScale, sub_sub_cancel] using h.symm
    _ = ∫ y, a ^ 2 • H (a • y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [L.lowSymbol_kernel_scaling]
      dsimp [H, a]
      rw [inv_smul_smul₀ (by positivity : (2 : ℝ) ^ N ≠ 0)]
      simp only [mul_assoc]
    _ = a ^ 2 • ∫ y, H (a • y) := integral_smul _ _
    _ = a ^ 2 • ((a ^ 2)⁻¹ • ∫ y, H y) := by
      rw [Measure.integral_comp_smul_of_nonneg volume H a (hR := ha.le), hd]
    _ = _ := by rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_smul]

/-- Uniform pointwise bound, independent of the frequency scale. -/
theorem FrequencyCutoff.norm_lowAtScale_le (L : FrequencyCutoff) (N : ℕ)
    {f : Plane → ℂ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : Plane) :
    ‖L.lowAtScale N f x‖ ≤ (∫ y, ‖L.lowKernel y‖) * B := by
  rw [L.lowAtScale_eq_rescaled]
  have hb := L.lowKernel_integrable.norm.mul_const B
  refine (norm_integral_le_of_norm_le hb (ae_of_all _ fun y => ?_)).trans_eq ?_
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
  · exact integral_mul_const _ _

/-- Actual low-pass convolutions converge at every point of a bounded
continuous test. No ambient almost-everywhere representative is selected. -/
theorem FrequencyCutoff.lowAtScale_tendsto (L : FrequencyCutoff)
    {f : Plane → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B)
    (x : Plane) : Tendsto (fun N => L.lowAtScale N f x) atTop (𝓝 (f x)) := by
  have hscale : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have ht := tendsto_integral_of_dominated_convergence
    (fun y : Plane => ‖L.lowKernel y‖ * B)
    (F := fun N y => L.lowKernel y * f (x - ((2 : ℝ) ^ N)⁻¹ • y))
    (f := fun y => L.lowKernel y * f x)
    (fun N => (L.lowKernel_smooth.continuous.mul
      (hf.comp (continuous_const.sub (continuous_const.smul continuous_id)))).aestronglyMeasurable)
    (L.lowKernel_integrable.norm.mul_const B)
    (fun N => ae_of_all _ fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _))
    (ae_of_all _ fun y => by
      have hxy : Tendsto (fun N : ℕ => x - ((2 : ℝ) ^ N)⁻¹ • y) atTop (𝓝 x) := by
        simpa using tendsto_const_nhds.sub (hscale.smul_const y)
      exact tendsto_const_nhds.mul (hf.continuousAt.tendsto.comp hxy))
  simpa only [← L.lowAtScale_eq_rescaled, integral_mul_const,
    L.integral_lowKernel, one_mul] using ht

theorem inverseFourierIntegrand_integrable (m : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) (x : Plane) :
    Integrable (fun ξ => (m ξ : ℂ) * Complex.exp
      (((2 * Real.pi * fourierPhase x ξ : ℝ) : ℂ) * Complex.I)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · apply (Complex.continuous_ofReal.comp hm.continuous).mul
    unfold fourierPhase
    fun_prop
  · exact (hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right

theorem inverseFourierIntegral_sub (m n : Plane → ℝ)
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (hn : ContDiff ℝ ∞ n) (hd : HasCompactSupport n) (x : Plane) :
    inverseFourierIntegral (m - n) x = inverseFourierIntegral m x - inverseFourierIntegral n x := by
  unfold inverseFourierIntegral
  simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul]
  exact integral_sub (inverseFourierIntegrand_integrable m hm hc x)
    (inverseFourierIntegrand_integrable n hn hd x)

theorem FrequencyCutoff.bandKernel_eq_lowSymbol_sub (L : FrequencyCutoff) (k : ℕ)
    (x : Plane) : L.bandKernel k x =
      inverseFourierIntegral (L.lowSymbol (k + 1)) x -
        inverseFourierIntegral (L.lowSymbol k) x :=
  inverseFourierIntegral_sub _ _ (L.lowSymbol_smooth (k + 1))
    (L.lowSymbol_compact (k + 1)) (L.lowSymbol_smooth k) (L.lowSymbol_compact k) x

theorem FrequencyCutoff.lowAtScale_integrand_integrable (L : FrequencyCutoff) (N : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) (x : Plane) :
    Integrable (fun y => inverseFourierIntegral (L.lowSymbol N) (x - y) * f y) := by
  have hK := (inverseFourierIntegral_memLp _ (L.lowSymbol_smooth N)
    (L.lowSymbol_compact N) ⊤).comp_measurePreserving
      (Measure.measurePreserving_sub_left volume x)
  exact memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hf).smul hK)

theorem FrequencyCutoff.band_eq_lowAtScale_sub (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) (x : Plane) :
    L.band k f x = L.lowAtScale (k + 1) f x - L.lowAtScale k f x := by
  unfold band lowAtScale
  simp only [L.bandKernel_eq_lowSymbol_sub, sub_mul]
  exact integral_sub (L.lowAtScale_integrand_integrable (k + 1) hf x)
    (L.lowAtScale_integrand_integrable k hf x)

/-- The finite Littlewood--Paley identity for the actual convolution operators. -/
theorem FrequencyCutoff.finite_reconstruction (L : FrequencyCutoff) (N : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) (x : Plane) :
    L.low f x + ∑ k ∈ Finset.range N, L.band k f x = L.lowAtScale N f x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, L.band_eq_lowAtScale_sub N hf x]
    ring

theorem FrequencyCutoff.lowAtScale_continuous (L : FrequencyCutoff) (N : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) : Continuous (L.lowAtScale N f) := by
  let K : Plane → ℂ := inverseFourierIntegral (L.lowSymbol N)
  have hcont : Continuous K :=
    (inverseFourierIntegral_smooth _ (L.lowSymbol_smooth N) (L.lowSymbol_compact N)).continuous
  obtain ⟨C, _, hC⟩ := inverseFourierIntegral_rapid_decay _
    (L.lowSymbol_smooth N) (L.lowSymbol_compact N) 0
  have hb : BddAbove (range (fun x => ‖K x‖)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa [K] using hC x
  have he : L.lowAtScale N f = f ⋆[ContinuousLinearMap.mul ℂ ℂ] K := by
    funext x
    simp only [lowAtScale, convolution_def, ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    filter_upwards [] with y
    exact mul_comm _ _
  rw [he]
  exact hb.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) hf hcont

theorem FrequencyCutoff.band_continuous (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) : Continuous (L.band k f) := by
  have he : L.band k f = L.lowAtScale (k + 1) f - L.lowAtScale k f :=
    funext (L.band_eq_lowAtScale_sub k hf)
  rw [he]
  exact (L.lowAtScale_continuous (k + 1) hf).sub (L.lowAtScale_continuous k hf)

theorem cutoffSlice_hasCompactSupport {d : ℕ} (χ : Cutoff d)
    (hc : HasCompactSupport χ) (q : Parameters 2 d) :
    HasCompactSupport (fun t => χ (t, q)) := by
  apply HasCompactSupport.intro (hc.image continuous_fst)
  intro t ht
  exact image_eq_zero_of_notMem_tsupport (fun h => ht ⟨(t, q), h, rfl⟩)

/-- Actual ambient continuity is required only on the cutoff support.
An arbitrary extension of gamma outside this support is harmless. -/
theorem Family.cutoffIntegrand_continuous {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : Continuous χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) :
    Continuous (fun x : ℝ × Parameters 2 d => (χ x : ℂ) * f (x.1, G.γ x.1 x.2)) := by
  have he : tsupport (fun x => (χ x : ℂ)) = tsupport χ := by
    unfold tsupport
    congr 1
    ext x
    simp
  apply continuous_of_tsupport
  intro x hx
  have hxχ : x ∈ tsupport χ := he ▸ (tsupport_mul_subset_left hx)
  exact (Complex.continuous_ofReal.comp hχ).continuousAt.mul
    (hf.continuousAt.comp (continuousAt_fst.prodMk (hγ x hxχ)))

theorem Family.cutoffIntegrand_integrable {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) (q : Parameters 2 d) :
    Integrable (fun t => (χ (t, q) : ℂ) * f (G.graphMap q t)) := by
  have hcont : Continuous (fun t => (χ (t, q) : ℂ) * f (G.graphMap q t)) :=
    (G.cutoffIntegrand_continuous χ hχ hγ hf).comp
      (continuous_id.prodMk continuous_const)
  apply Continuous.integrable_of_hasCompactSupport hcont
  exact ((cutoffSlice_hasCompactSupport χ hc q).comp_left
    (g := Complex.ofRealCLM) rfl).mul_right

theorem Family.cutoffAverage_add_continuous {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f g : Plane → ℂ} (hf : Continuous f) (hg : Continuous g) (q : Parameters 2 d) :
    G.cutoffAverage χ (f + g) q = G.cutoffAverage χ f q + G.cutoffAverage χ g q := by
  unfold cutoffAverage
  simp only [Pi.add_apply, mul_add]
  exact integral_add (G.cutoffIntegrand_integrable χ hχ hc hγ hf q)
    (G.cutoffIntegrand_integrable χ hχ hc hγ hg q)

theorem Family.cutoffAverage_finsetSum_continuous {d : ℕ} {ι : Type*} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (s : Finset ι) (f : ι → Plane → ℂ) (hf : ∀ i ∈ s, Continuous (f i))
    (q : Parameters 2 d) :
    G.cutoffAverage χ (fun x => ∑ i ∈ s, f i x) q =
      ∑ i ∈ s, G.cutoffAverage χ (f i) q := by
  unfold cutoffAverage
  simp only [Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => G.cutoffIntegrand_integrable χ hχ hc hγ (hf i hi) q)

/-- Dominated convergence along each actual cutoff curve. -/
theorem Family.cutoffAverage_lowAtScale_tendsto {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) (hfi : Integrable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (q : Parameters 2 d) :
    Tendsto (fun N => G.cutoffAverage χ (L.lowAtScale N f) q) atTop
      (𝓝 (G.cutoffAverage χ f q)) := by
  let A : ℝ := (∫ y, ‖L.lowKernel y‖) * B
  have hχq : Integrable (fun t => ‖χ (t, q)‖) :=
    ((hχ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (cutoffSlice_hasCompactSupport χ hc q)).norm
  apply tendsto_integral_of_dominated_convergence (fun t => ‖χ (t, q)‖ * A)
  · intro N
    exact (G.cutoffIntegrand_integrable χ hχ hc hγ
      (L.lowAtScale_continuous N hfi) q).aestronglyMeasurable
  · exact hχq.mul_const A
  · intro N
    filter_upwards [] with t
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (L.norm_lowAtScale_le N hB _) (norm_nonneg _)
  · filter_upwards [] with t
    exact tendsto_const_nhds.mul (L.lowAtScale_tendsto hf hB _)

theorem Family.cutoffAverage_finite_reconstruction {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hfi : Integrable f) (N : ℕ) (q : Parameters 2 d) :
    G.cutoffAverage χ (L.low f) q +
      ∑ k ∈ Finset.range N, G.cutoffAverage χ (L.band k f) q =
        G.cutoffAverage χ (L.lowAtScale N f) q := by
  have hsum : Continuous (fun x => ∑ k ∈ Finset.range N, L.band k f x) :=
    continuous_finsetSum _ (fun k _ => L.band_continuous k hfi)
  rw [← G.cutoffAverage_finsetSum_continuous χ hχ hc hγ (Finset.range N)
    (fun k => L.band k f) (fun k _ => L.band_continuous k hfi) q]
  rw [← G.cutoffAverage_add_continuous χ hχ hc hγ (L.low_continuous hfi) hsum q]
  congr 1
  funext x
  exact L.finite_reconstruction N hfi x

/-- Pointwise reconstruction bound on every actual cutoff curve. This is
the triangle inequality applied before passing to the reconstructed limit. -/
theorem Family.cutoffAverage_reconstruction_majorant {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) (hfi : Integrable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (q : Parameters 2 d) :
    ‖G.cutoffAverage χ f q‖ₑ ≤ ‖G.cutoffAverage χ (L.low f) q‖ₑ +
      ∑' k, ‖G.cutoffAverage χ (L.band k f) q‖ₑ := by
  apply le_of_tendsto' (G.cutoffAverage_lowAtScale_tendsto χ L hχ hc hγ hf hfi hB q).enorm
  intro N
  rw [← G.cutoffAverage_finite_reconstruction χ L hχ hc hγ hfi N q]
  calc
    _ ≤ ‖G.cutoffAverage χ (L.low f) q‖ₑ +
        ‖∑ k ∈ Finset.range N, G.cutoffAverage χ (L.band k f) q‖ₑ := enorm_add_le _ _
    _ ≤ ‖G.cutoffAverage χ (L.low f) q‖ₑ +
        ∑ k ∈ Finset.range N, ‖G.cutoffAverage χ (L.band k f) q‖ₑ := by
      exact add_le_add le_rfl (enorm_sum_le (Finset.range N)
        (fun k => G.cutoffAverage χ (L.band k f) q))
    _ ≤ _ := add_le_add le_rfl (ENNReal.sum_le_tsum (Finset.range N))

end PlanarNikodym
