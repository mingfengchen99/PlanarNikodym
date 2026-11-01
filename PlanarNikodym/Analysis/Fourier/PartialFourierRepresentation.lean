import PlanarNikodym.Analysis.Fourier.MicrolocalBandRepresentation

/-! An actual partial Fourier representation of the main frequency piece.
The compact frequency symbol remains inside `weightedPartialFourierData`;
this function is not identified with an unweighted partial inverse Fourier
transform. All changes of integration order are justified by integrability. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

def oneDimFourierCharacter (r x ξ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * r * x * ξ : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_oneDimFourierCharacter (r x ξ : ℝ) :
    ‖oneDimFourierCharacter r x ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem Family.planeFourierCharacter_split {d : ℕ} (G : Family 2 d)
    (q : Parameters 2 d) (r t ξ₁ ξ₂ : ℝ) :
    planeFourierCharacter (G.graphMap q t) (r • (ξ₁, ξ₂)) =
      oneDimFourierCharacter r t ξ₁ * oneDimFourierCharacter r (G.γ t q) ξ₂ := by
  have he : 2 * Real.pi * fourierPhase (G.graphMap q t) (r • (ξ₁, ξ₂)) =
      2 * Real.pi * r * t * ξ₁ + 2 * Real.pi * r * G.γ t q * ξ₂ := by
    change 2 * Real.pi * (t * (r * ξ₁) + G.γ t q * (r * ξ₂)) = _
    ring
  unfold planeFourierCharacter oneDimFourierCharacter
  rw [he, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Partial inverse Fourier data for a general frequency amplitude. -/
def partialFourierData (a : Plane → ℂ) (r t ξ₂ : ℝ) : ℂ :=
  ∫ ξ₁ : ℝ, a (ξ₁, ξ₂) * oneDimFourierCharacter r t ξ₁

/-- The actual compact symbol is included in this data, together with the
Fourier transform evaluated at the dilated frequency. -/
def weightedPartialFourierData (m : Plane → ℝ) (f : Plane → ℂ) (r t ξ₂ : ℝ) : ℂ :=
  partialFourierData (fun ξ => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) r t ξ₂

theorem norm_partialFourierData_le (a : Plane → ℂ) (r t ξ₂ : ℝ) :
    ‖partialFourierData a r t ξ₂‖ ≤ ∫ ξ₁ : ℝ, ‖a (ξ₁, ξ₂)‖ := by
  calc
    _ ≤ ∫ ξ₁ : ℝ, ‖a (ξ₁, ξ₂) * oneDimFourierCharacter r t ξ₁‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp

theorem stronglyMeasurable_partialFourierData {a : Plane → ℂ} (ha : Continuous a) (r : ℝ) :
    StronglyMeasurable (fun x : ℝ × ℝ => partialFourierData a r x.1 x.2) := by
  have hF : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      a (p.2, p.1.2) * oneDimFourierCharacter r p.1.1 p.2) := by
    apply (ha.comp (continuous_snd.prodMk continuous_fst.snd)).mul
    unfold oneDimFourierCharacter
    fun_prop
  exact hF.stronglyMeasurable.integral_prod_right'

/-- Absolute integrability for the original time and two-dimensional
frequency variables, including arbitrary real frequency dilations. -/
theorem Family.integrable_scaled_cutoffOscillatoryProduct {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℂ} (ha : Integrable a) (q : Parameters 2 d) (r : ℝ) :
    Integrable (fun p : ℝ × Plane =>
      ((χ (p.1, q) : ℂ) * planeFourierCharacter (G.graphMap q p.1) (r • p.2)) * a p.2)
      (volume.prod volume) := by
  have hslice : Integrable (fun t : ℝ => χ (t, q)) :=
    (hχ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (cutoffSlice_hasCompactSupport χ hc q)
  have hC : Continuous (fun p : ℝ × Plane =>
      (χ (p.1, q) : ℂ) * planeFourierCharacter (G.graphMap q p.1) (r • p.2)) :=
    (G.continuous_cutoffOscillatoryIntegrand χ hχ hγ q).comp
      (continuous_fst.prodMk (continuous_const.smul continuous_snd))
  apply (hslice.norm.mul_prod ha.norm).mono'
  · exact hC.aestronglyMeasurable.mul ha.aestronglyMeasurable.comp_snd
  · filter_upwards [] with p
    simp [Complex.norm_real]

theorem Family.scaled_cutoffOscillatoryAmplitude_mul_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℂ} (ha : Integrable a) (q : Parameters 2 d) (r : ℝ) :
    Integrable (fun ξ => a ξ * G.cutoffOscillatoryAmplitude χ q (r • ξ)) := by
  apply (G.integrable_scaled_cutoffOscillatoryProduct χ hχ hc hγ ha q r).integral_prod_right.congr
  filter_upwards [] with ξ
  simp only [integral_mul_const, Family.cutoffOscillatoryAmplitude]
  ring

/-- The reduced time/vertical-frequency integrand is itself absolutely
integrable; the bound uses the actual marginal integral of `‖a‖`. -/
theorem Family.integrable_partialFourierExtension {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℂ} (ha : Continuous a) (hai : Integrable a)
    (q : Parameters 2 d) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => (χ (p.1, q) : ℂ) * partialFourierData a r p.1 p.2 *
      oneDimFourierCharacter r (G.γ p.1 q) p.2) (volume.prod volume) := by
  have hslice : Integrable (fun t : ℝ => χ (t, q)) :=
    (hχ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (cutoffSlice_hasCompactSupport χ hc q)
  have hC : Continuous (fun p : ℝ × ℝ => (χ (p.1, q) : ℂ) *
      oneDimFourierCharacter r (G.γ p.1 q) p.2) := by
    have hmap : Continuous (fun p : ℝ × ℝ => (p.1, r • ((0, p.2) : Plane))) :=
      continuous_fst.prodMk (continuous_const.smul (continuous_const.prodMk continuous_snd))
    have h := (G.continuous_cutoffOscillatoryIntegrand χ hχ hγ q).comp
      hmap
    convert h using 1
    funext p
    change (χ (p.1, q) : ℂ) * oneDimFourierCharacter r (G.γ p.1 q) p.2 =
      (χ (p.1, q) : ℂ) * planeFourierCharacter (G.graphMap q p.1) (r • (0, p.2))
    rw [G.planeFourierCharacter_split q r p.1 0 p.2]
    simp only [oneDimFourierCharacter, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul]
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (χ (p.1, q) : ℂ) * partialFourierData a r p.1 p.2 *
        oneDimFourierCharacter r (G.γ p.1 q) p.2) (volume.prod volume) := by
    have h : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        ((χ (p.1, q) : ℂ) * oneDimFourierCharacter r (G.γ p.1 q) p.2) *
          partialFourierData a r p.1 p.2) (volume.prod volume) :=
      hC.aestronglyMeasurable.mul
        (stronglyMeasurable_partialFourierData ha r).aestronglyMeasurable
    convert h using 1
    funext p
    ring
  apply (hslice.norm.mul_prod hai.norm.integral_prod_right).mono' hm
  filter_upwards [] with p
  simp only [norm_mul, norm_oneDimFourierCharacter, mul_one, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (norm_partialFourierData_le a r p.1 p.2) (norm_nonneg _)

/-- Exact extension representation after partial inversion in the horizontal
frequency. Both Fubini exchanges use the integrability established above. -/
theorem Family.scaled_cutoffOscillatoryIntegral_eq_partialExtension {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℂ} (ha : Continuous a) (hai : Integrable a)
    (q : Parameters 2 d) (r : ℝ) :
    (∫ ξ : Plane, a ξ * G.cutoffOscillatoryAmplitude χ q (r • ξ)) =
      ∫ ξ₂ : ℝ, ∫ t : ℝ, (χ (t, q) : ℂ) * partialFourierData a r t ξ₂ *
        oneDimFourierCharacter r (G.γ t q) ξ₂ := by
  calc
    _ = ∫ ξ : Plane, ∫ t : ℝ,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) (r • ξ)) * a ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [Family.cutoffOscillatoryAmplitude, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = ∫ t : ℝ, ∫ ξ : Plane,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) (r • ξ)) * a ξ :=
      (integral_integral_swap (G.integrable_scaled_cutoffOscillatoryProduct χ hχ hc hγ hai q r)).symm
    _ = ∫ t : ℝ, ∫ ξ₂ : ℝ, (χ (t, q) : ℂ) * partialFourierData a r t ξ₂ *
        oneDimFourierCharacter r (G.γ t q) ξ₂ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hF : Integrable (fun ξ : Plane =>
          ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) (r • ξ)) * a ξ) := by
        apply (hai.norm.const_mul ‖(χ (t, q) : ℂ)‖).mono'
        · apply Continuous.aestronglyMeasurable
          exact (continuous_const.mul (continuous_planeFourierCharacter.comp
            (continuous_const.prodMk (continuous_const.smul continuous_id)))).mul ha
        · filter_upwards [] with ξ
          simp
      rw [Measure.volume_eq_prod] at hF ⊢
      rw [integral_prod_symm _ hF]
      apply integral_congr_ae
      filter_upwards [] with ξ₂
      simp_rw [G.planeFourierCharacter_split q r t]
      rw [partialFourierData, ← integral_const_mul, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with ξ₁
      ring
    _ = _ := integral_integral_swap (G.integrable_partialFourierExtension χ hχ hc hγ ha hai q r)

theorem weighted_scaledFourierData_continuous {m : Plane → ℝ} (hm : Continuous m)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    Continuous (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
  (Complex.continuous_ofReal.comp hm).mul
    ((continuous_planeFourierIntegral hf).comp (continuous_const.smul continuous_id))

theorem weighted_scaledFourierData_integrable {m : Plane → ℝ} (hm : Continuous m)
    (hc : HasCompactSupport m) {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    Integrable (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
  (weighted_scaledFourierData_continuous hm hf r).integrable_of_hasCompactSupport
    (hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right

/-- For the actual compact frequency data the partial inverse integral is
absolutely convergent at every time and every vertical frequency. -/
theorem weightedPartialFourierIntegrand_integrable {m : Plane → ℝ} (hm : Continuous m)
    (hc : HasCompactSupport m) {f : Plane → ℂ} (hf : Integrable f) (r t ξ₂ : ℝ) :
    Integrable (fun ξ₁ : ℝ => ((m (ξ₁, ξ₂) : ℝ) : ℂ) *
      planeFourierIntegral f (r • (ξ₁, ξ₂)) * oneDimFourierCharacter r t ξ₁) := by
  have hcont : Continuous (fun ξ₁ : ℝ => ((m (ξ₁, ξ₂) : ℝ) : ℂ) *
      planeFourierIntegral f (r • (ξ₁, ξ₂)) * oneDimFourierCharacter r t ξ₁) := by
    apply ((weighted_scaledFourierData_continuous hm hf r).comp
      (continuous_id.prodMk continuous_const)).mul
    unfold oneDimFourierCharacter
    fun_prop
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (hc.isCompact.image continuous_fst)
  intro ξ₁ hξ₁
  have hzero : m (ξ₁, ξ₂) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx => hξ₁ ⟨(ξ₁, ξ₂), hx, rfl⟩)
  simp only [hzero, Complex.ofReal_zero, zero_mul]

theorem Family.weighted_scaled_cutoffOscillatoryIntegral_eq_partialExtension {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (m : Plane → ℝ) (hm : Continuous m) (hcm : HasCompactSupport m)
    {f : Plane → ℂ} (hf : Integrable f) (q : Parameters 2 d) (r : ℝ) :
    (∫ ξ : Plane, (m ξ : ℂ) * planeFourierIntegral f (r • ξ) *
      G.cutoffOscillatoryAmplitude χ q (r • ξ)) =
      ∫ ξ₂ : ℝ, ∫ t : ℝ, (χ (t, q) : ℂ) * weightedPartialFourierData m f r t ξ₂ *
        oneDimFourierCharacter r (G.γ t q) ξ₂ :=
  G.scaled_cutoffOscillatoryIntegral_eq_partialExtension χ hχ hcχ hγ
    (weighted_scaledFourierData_continuous hm hf r)
    (weighted_scaledFourierData_integrable hm hcm hf r) q r

/-- The true band average equals a two-variable extension main term plus
its actual frequency-space error term. The band symbol and vertical cutoff
are retained inside the weighted partial data, at the normalized scale. -/
theorem Family.cutoffAverage_band_eq_partialExtension_add_error {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff)
    (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (β : ℝ → ℝ) (hβ : Continuous β) {f : Plane → ℂ} (hf : Integrable f)
    (k : ℕ) (q : Parameters 2 d) :
    G.cutoffAverage χ (L.band k f) q =
      (((2 : ℝ) ^ k) ^ 2) •
        (∫ ξ₂ : ℝ, ∫ t : ℝ, (χ (t, q) : ℂ) *
          weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2)
            f ((2 : ℝ) ^ k) t ξ₂ * oneDimFourierCharacter ((2 : ℝ) ^ k) (G.γ t q) ξ₂) +
      (((2 : ℝ) ^ k) ^ 2) •
        ∫ ξ : Plane, ((L.bandSymbol 0 ξ * (1 - β ξ.2) : ℝ) : ℂ) *
          planeFourierIntegral f ((2 : ℝ) ^ k • ξ) *
            G.cutoffOscillatoryAmplitude χ q ((2 : ℝ) ^ k • ξ) := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  let e : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * (1 - β ξ.2)
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.comp continuous_snd)
  have he : Continuous e := (L.bandSymbol_smooth 0).continuous.mul
    (continuous_const.sub (hβ.comp continuous_snd))
  have hcm : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  have hce : HasCompactSupport e := (L.bandSymbol_compact 0).mul_right
  have hmi := G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hcχ hγ
    (weighted_scaledFourierData_integrable hm hcm hf ((2 : ℝ) ^ k)) q ((2 : ℝ) ^ k)
  have hei := G.scaled_cutoffOscillatoryAmplitude_mul_integrable χ hχ hcχ hγ
    (weighted_scaledFourierData_integrable he hce hf ((2 : ℝ) ^ k)) q ((2 : ℝ) ^ k)
  rw [← G.weighted_scaled_cutoffOscillatoryIntegral_eq_partialExtension χ hχ hcχ hγ
      m hm hcm hf q ((2 : ℝ) ^ k),
    G.cutoffAverage_band_eq_rescaled_oscillatoryIntegral χ L hχ hcχ hγ hf k q,
    ← smul_add, ← integral_add hmi hei]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [m, e, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

end PlanarNikodym
