import PlanarNikodym.Analysis.Fourier.MicrolocalErrorLp
import PlanarNikodym.Analysis.Localization.ScaleTimeLocalization

/-! The genuine L∞ endpoint for the partial-Fourier main term. The
frequency Jacobian cancels the physical kernel dilation exactly. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal

namespace PlanarNikodym

set_option maxHeartbeats 800000

/-- The physical convolution for a fixed normalized symbol, retaining the
original two-dimensional frequency Jacobian. -/
def scaledFrequencyConvolution (m : Plane → ℝ) (r : ℝ) (f : Plane → ℂ)
    (x : Plane) : ℂ :=
  r ^ 2 • ∫ y : Plane, inverseFourierIntegral m (r • (x - y)) * f y

/-- The scaled convolution is the actual Fourier multiplier integral. -/
theorem scaledFrequencyConvolution_eq_fourierIntegral
    {m : Plane → ℝ} (hm : Continuous m) (hmi : Integrable m)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (x : Plane) :
    scaledFrequencyConvolution m r f x =
      r ^ 2 • ∫ ξ : Plane, (m ξ : ℂ) * planeFourierIntegral f (r • ξ) *
        planeFourierCharacter x (r • ξ) := by
  have hprod : Integrable (fun p : Plane × Plane =>
      (m p.1 : ℂ) * planeFourierCharacter (x - p.2) (r • p.1) * f p.2)
      (volume.prod volume) := by
    apply (hmi.norm.mul_prod hf.norm).mono'
    · exact ((Complex.continuous_ofReal.comp (hm.comp continuous_fst)).mul
        (continuous_planeFourierCharacter.comp
          ((continuous_const.sub continuous_snd).prodMk
            (continuous_const.smul continuous_fst)))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable.comp_snd
    · filter_upwards [] with p
      simp [Complex.norm_real]
  unfold scaledFrequencyConvolution
  congr 1
  calc
    _ = ∫ y : Plane, ∫ ξ : Plane,
        (m ξ : ℂ) * planeFourierCharacter (x - y) (r • ξ) * f y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [inverseFourierIntegral, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with ξ
      change (m ξ : ℂ) * planeFourierCharacter (r • (x - y)) ξ * f y = _
      rw [planeFourierCharacter_smul_swap]
    _ = ∫ ξ : Plane, ∫ y : Plane,
        (m ξ : ℂ) * planeFourierCharacter (x - y) (r • ξ) * f y :=
      (integral_integral_swap hprod).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp_rw [planeFourierCharacter_sub]
      rw [show (fun y : Plane =>
          (m ξ : ℂ) * (planeFourierCharacter x (r • ξ) *
            planeFourierCharacter (-y) (r • ξ)) * f y) =
          (fun y : Plane => ((m ξ : ℂ) * planeFourierCharacter x (r • ξ)) *
            (f y * planeFourierCharacter (-y) (r • ξ))) by funext y; ring,
        integral_const_mul]
      simp only [planeFourierIntegral]
      ring

/-- Exact cancellation of the two-dimensional Jacobian in kernel mass. -/
theorem scaled_frequency_kernel_L1_mass {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) {r : ℝ} (hr : 0 < r)
    (x : Plane) :
    ENNReal.ofReal (r ^ 2) *
        eLpNorm (fun y : Plane => inverseFourierIntegral m (r • (x - y))) 1 volume =
      ENNReal.ofReal (∫ y : Plane, ‖inverseFourierIntegral m y‖) := by
  have hi := ((inverseFourierIntegral_integrable m hm hc).comp_smul hr.ne').comp_sub_left x
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi,
    ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  rw [integral_sub_left_eq_self (fun y : Plane => ‖inverseFourierIntegral m (r • y)‖),
    Measure.integral_comp_smul_of_nonneg (volume : Measure Plane)
      (fun y => ‖inverseFourierIntegral m y‖) r (hR := hr.le)]
  simp only [Plane, Module.finrank_prod, Module.finrank_self, Nat.reduceAdd, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

/-- Uniform L∞ bound for the normalized multiplier at every positive
frequency scale and every spatial point. The constant is the fixed kernel's
L¹ mass; no factor depending on the frequency remains. -/
theorem scaledFrequencyConvolution_enorm_le_LInfinity {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) {r : ℝ} (hr : 0 < r)
    {f : Plane → ℂ} (hf : Integrable f) (x : Plane) :
    ‖scaledFrequencyConvolution m r f x‖ₑ ≤
      ENNReal.ofReal (∫ y : Plane, ‖inverseFourierIntegral m y‖) * eLpNorm f ∞ volume := by
  let K : Plane → ℂ := fun y => inverseFourierIntegral m (r • (x - y))
  have hK : Continuous K :=
    (inverseFourierIntegral_smooth m hm hc).continuous.comp
      (continuous_const.smul (continuous_const.sub continuous_id))
  have hHolder : (∫⁻ y : Plane, ‖K y * f y‖ₑ) ≤
      eLpNorm K 1 volume * eLpNorm f ∞ volume := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℂ) hf.aestronglyMeasurable hK.aestronglyMeasurable
  unfold scaledFrequencyConvolution
  rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg r)]
  calc
    _ ≤ ENNReal.ofReal (r ^ 2) * (∫⁻ y : Plane, ‖K y * f y‖ₑ) := by
      exact mul_le_mul_right (enorm_integral_le_lintegral_enorm (fun y : Plane => K y * f y)) _
    _ ≤ ENNReal.ofReal (r ^ 2) * (eLpNorm K 1 volume * eLpNorm f ∞ volume) := by
      exact mul_le_mul_right hHolder _
    _ = _ := by rw [← mul_assoc, scaled_frequency_kernel_L1_mass hm hc hr x]

/-- The actual main extension is the curve average of the uniformly
bounded physical multiplier. -/
theorem Family.cutoffPartialExtension_eq_scaledFrequencyConvolution {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (q : Parameters 2 d) :
    G.cutoffPartialExtension χ L β r f q =
      G.cutoffAverage χ
        (scaledFrequencyConvolution (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) r f) q := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.comp continuous_snd)
  have hcm : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  have hmi : Integrable m := hm.integrable_of_hasCompactSupport hcm
  rw [Family.cutoffPartialExtension,
    ← G.weighted_scaled_cutoffOscillatoryIntegral_eq_partialExtension χ hχ hcχ hγ
      m hm hcm hf q r]
  unfold Family.cutoffAverage
  change r ^ 2 • _ = ∫ t : ℝ, (χ (t, q) : ℂ) * scaledFrequencyConvolution m r f (G.graphMap q t)
  simp_rw [scaledFrequencyConvolution_eq_fourierIntegral hm hmi hf r]
  simp_rw [mul_smul_comm]
  rw [integral_smul]
  congr 1
  calc
    _ = ∫ ξ : Plane, ∫ t : ℝ,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) (r • ξ)) *
          ((m ξ : ℂ) * planeFourierIntegral f (r • ξ)) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [Family.cutoffOscillatoryAmplitude, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = ∫ t : ℝ, ∫ ξ : Plane,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) (r • ξ)) *
          ((m ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
      (integral_integral_swap (G.integrable_scaled_cutoffOscillatoryProduct χ hχ hcχ hγ
        (weighted_scaledFourierData_integrable hm hcm hf r) q r)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      ring

/-- The pointwise endpoint for the actual main term uses precisely the
L¹ mass of the time cutoff and of the fixed multiplier kernel. -/
theorem Family.cutoffPartialExtension_enorm_le_LInfinity {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {f : Plane → ℂ} (hf : Integrable f) {r : ℝ} (hr : 0 < r)
    (q : Parameters 2 d) :
    ‖G.cutoffPartialExtension χ L β r f q‖ₑ ≤
      ENNReal.ofReal ((∫ t : ℝ, ‖χ (t, q)‖) *
        (∫ y : Plane, ‖inverseFourierIntegral
          (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) y‖)) * eLpNorm f ∞ volume := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : ContDiff ℝ ∞ m := (L.bandSymbol_smooth 0).mul (hβ.comp contDiff_snd)
  have hcm : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  have hi : Integrable (fun t : ℝ => χ (t, q)) :=
    (hχ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (cutoffSlice_hasCompactSupport χ hcχ q)
  rw [G.cutoffPartialExtension_eq_scaledFrequencyConvolution χ hχ hcχ hγ L β
    hβ.continuous hf r q]
  unfold Family.cutoffAverage
  calc
    _ ≤ ∫⁻ t : ℝ, ‖(χ (t, q) : ℂ) * scaledFrequencyConvolution m r f
        (G.graphMap q t)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t : ℝ, ‖χ (t, q)‖ₑ * (ENNReal.ofReal
        (∫ y : Plane, ‖inverseFourierIntegral m y‖) * eLpNorm f ∞ volume) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [← ofReal_norm, norm_mul, Complex.norm_real,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
      exact mul_le_mul_right (scaledFrequencyConvolution_enorm_le_LInfinity hm hcm hr hf _) _
    _ = _ := by
      have hmeas : Measurable (fun t : ℝ => ‖χ (t, q)‖ₑ) :=
        (hχ.comp (continuous_id.prodMk (continuous_const (y := q)))).enorm.measurable
      rw [lintegral_mul_const _ hmeas]
      rw [← ofReal_integral_norm_eq_lintegral_enorm hi,
        ← mul_assoc, ← ENNReal.ofReal_mul (integral_nonneg (fun _ => norm_nonneg _))]

/-- The actual localized time cutoff has L¹ mass bounded by its ambient
supremum times twice the slice scale, uniformly in every slice center. -/
theorem integral_norm_scaleTimeLocalizedCutoff_le {d : ℕ} (χ : Cutoff d)
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ) (B : ℝ) (_hB : 0 ≤ B)
    (hb : ∀ x, ‖χ x‖ ≤ B) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ)
    (q : Parameters 2 d) :
    (∫ t : ℝ, ‖scaleTimeLocalizedCutoff χ a δ i (t, q)‖) ≤ 2 * B * δ := by
  let J : Set ℝ := Icc (a + ((i : ℝ) - 1) * δ) (a + ((i : ℝ) + 1) * δ)
  have hcont : Continuous (scaleTimeLocalizedCutoff χ a δ i) :=
    by
      change Continuous (fun x : ℝ × Parameters 2 d => χ x * scaleTimeCutoff a δ i x.1)
      exact hχ.mul ((contDiff_scaleTimeCutoff a δ i).continuous.comp continuous_fst)
  have hi : Integrable (fun t : ℝ => scaleTimeLocalizedCutoff χ a δ i (t, q)) :=
    (hcont.comp (continuous_id.prodMk (continuous_const (y := q)))).integrable_of_hasCompactSupport
      (cutoffSlice_hasCompactSupport (scaleTimeLocalizedCutoff χ a δ i)
        (hasCompactSupport_scaleTimeLocalizedCutoff hcχ a δ i) q)
  have hjm : MeasurableSet J := measurableSet_Icc
  have hjf : volume J ≠ (∞ : ℝ≥0∞) := (isCompact_Icc : IsCompact J).measure_ne_top
  have hJ : Integrable (J.indicator (fun _ : ℝ => B)) :=
    (integrable_indicator_iff hjm).mpr (integrableOn_const hjf)
  have hbound : ∀ t, ‖scaleTimeLocalizedCutoff χ a δ i (t, q)‖ ≤ J.indicator (fun _ => B) t := by
    intro t
    by_cases ht : t ∈ J
    · rw [indicator_of_mem ht]
      simp only [scaleTimeLocalizedCutoff, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (scaleTimeCutoff_nonneg a δ t i)]
      calc
        |χ (t, q)| * scaleTimeCutoff a δ i t ≤ |χ (t, q)| * 1 :=
          mul_le_mul_of_nonneg_left (scaleTimeCutoff_le_one a δ t i) (abs_nonneg _)
        _ ≤ B := by simpa only [mul_one, ← Real.norm_eq_abs] using hb (t, q)
    · rw [indicator_of_notMem ht]
      have hz : scaleTimeCutoff a δ i t = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => ht (tsupport_scaleTimeCutoff_subset a hδ i hs))
      simp [scaleTimeLocalizedCutoff, hz]
  calc
    _ ≤ ∫ t, J.indicator (fun _ : ℝ => B) t := integral_mono hi.norm hJ hbound
    _ = 2 * B * δ := by
      rw [integral_indicator hjm, setIntegral_const]
      simp only [J, Measure.real, Real.volume_Icc, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤
        (a + ((i : ℝ) + 1) * δ) - (a + ((i : ℝ) - 1) * δ))]
      ring

/-- A genuine uniform endpoint for all the actual time pieces. The
constant is chosen before the frequency scale, time scale, time translate,
piece index and input. It includes the sharp time-length factor `δ`. -/
theorem Family.exists_uniform_cutoffPartialExtension_time_piece_LInfinity {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ a δ : ℝ, 0 < δ → ∀ i : ℕ,
      ∀ f : Plane → ℂ, Integrable f →
      (∀ q, ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ a δ i) L β r f q‖ₑ ≤
        ENNReal.ofReal (C * δ) * eLpNorm f ∞ volume) ∧
      eLpNorm (G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ a δ i) L β r f) ∞ volume ≤
        ENNReal.ofReal (C * δ) * eLpNorm f ∞ volume := by
  obtain ⟨x₀, hb⟩ := hχ.norm.exists_forall_ge_of_hasCompactSupport hcχ.norm
  let B := ‖χ x₀‖
  let K := ∫ y : Plane, ‖inverseFourierIntegral
    (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) y‖
  have hB : 0 ≤ B := norm_nonneg _
  have hK : 0 ≤ K := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨2 * B * K, by positivity, ?_⟩
  intro r hr a δ hδ i f hf
  have hχi : Continuous (scaleTimeLocalizedCutoff χ a δ i) :=
    by
      change Continuous (fun x : ℝ × Parameters 2 d => χ x * scaleTimeCutoff a δ i x.1)
      exact hχ.mul ((contDiff_scaleTimeCutoff a δ i).continuous.comp continuous_fst)
  have hci : HasCompactSupport (scaleTimeLocalizedCutoff χ a δ i) :=
    hasCompactSupport_scaleTimeLocalizedCutoff hcχ a δ i
  have hγi : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff χ a δ i),
      ContinuousAt (fun x => G.γ x.1 x.2) x :=
    fun x hx => hγ x (tsupport_scaleTimeLocalizedCutoff_subset χ a δ i hx)
  have hout : ∀ q, ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ a δ i) L β r f q‖ₑ ≤
      ENNReal.ofReal ((2 * B * K) * δ) * eLpNorm f ∞ volume := by
    intro q
    apply (G.cutoffPartialExtension_enorm_le_LInfinity _ hχi hci hγi L β hβ hf hr q).trans
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (2 * B * δ) * K := mul_le_mul_of_nonneg_right
        (integral_norm_scaleTimeLocalizedCutoff_le χ hχ hcχ B hB hb a hδ i q) hK
      _ = _ := by ring
  refine ⟨hout, ?_⟩
  exact eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall hout)

end PlanarNikodym
