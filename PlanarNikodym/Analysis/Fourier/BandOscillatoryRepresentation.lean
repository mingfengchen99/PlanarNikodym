import PlanarNikodym.Analysis.Fourier.FourierReconstruction
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual absolutely convergent oscillatory representations of the dyadic
bands and of their smoothly localized curve averages. These identities do
not assert decay or a local smoothing estimate. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace PlanarNikodym

/-- The positive Fourier character for the normalization of `bandKernel`. -/
def planeFourierCharacter (x ξ : Plane) : ℂ :=
  Complex.exp (((2 * Real.pi * fourierPhase x ξ : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_planeFourierCharacter (x ξ : Plane) :
    ‖planeFourierCharacter x ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_planeFourierCharacter :
    Continuous (fun p : Plane × Plane => planeFourierCharacter p.1 p.2) := by
  unfold planeFourierCharacter fourierPhase
  fun_prop

theorem planeFourierCharacter_sub (x y ξ : Plane) :
    planeFourierCharacter (x - y) ξ =
      planeFourierCharacter x ξ * planeFourierCharacter (-y) ξ := by
  have hs : fourierPhase (x - y) ξ = fourierPhase x ξ + fourierPhase (-y) ξ := by
    change (x.1 - y.1) * ξ.1 + (x.2 - y.2) * ξ.2 =
      (x.1 * ξ.1 + x.2 * ξ.2) + ((-y.1) * ξ.1 + (-y.2) * ξ.2)
    ring
  unfold planeFourierCharacter
  rw [hs]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- An actual forward Fourier integral on the original product-norm plane. -/
def planeFourierIntegral (f : Plane → ℂ) (ξ : Plane) : ℂ :=
  ∫ y : Plane, f y * planeFourierCharacter (-y) ξ

/-- Compatibility with Mathlib's Fourier transform in Euclidean coordinates. -/
theorem planeFourierIntegral_eq_euclidean (f : Plane → ℂ) (ξ : Plane) :
    planeFourierIntegral f ξ =
      𝓕 (fun y : FourierPlane => f (WithLp.ofLp y)) (WithLp.toLp 2 ξ) := by
  rw [Real.fourier_eq']
  unfold planeFourierIntegral
  rw [← (WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 Plane).symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial,
    smul_eq_mul, planeFourierCharacter, fourierPhase]
  rw [mul_comm (f _)]
  congr 2
  congr 1
  apply congrArg (fun r : ℝ => (r : ℂ))
  change 2 * Real.pi * ((-(WithLp.ofLp y).1) * ξ.1 + (-(WithLp.ofLp y).2) * ξ.2) =
    -2 * Real.pi * (ξ.1 * (WithLp.ofLp y).1 + ξ.2 * (WithLp.ofLp y).2)
  ring

theorem planeFourierIntegrand_integrable {f : Plane → ℂ}
    (hf : Integrable f) (ξ : Plane) :
    Integrable (fun y => f y * planeFourierCharacter (-y) ξ) := by
  apply hf.mono
  · exact hf.aestronglyMeasurable.mul
      (continuous_planeFourierCharacter.comp
        (continuous_neg.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [] with y
    simp

theorem norm_planeFourierIntegral_le (f : Plane → ℂ) (ξ : Plane) :
    ‖planeFourierIntegral f ξ‖ ≤ ∫ y : Plane, ‖f y‖ := by
  calc
    _ ≤ ∫ y : Plane, ‖f y * planeFourierCharacter (-y) ξ‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp

theorem continuous_planeFourierIntegral {f : Plane → ℂ} (hf : Integrable f) :
    Continuous (planeFourierIntegral f) := by
  apply continuous_of_dominated (bound := fun y => ‖f y‖)
  · intro ξ
    exact (planeFourierIntegrand_integrable hf ξ).aestronglyMeasurable
  · intro ξ
    filter_upwards [] with y
    simp
  · exact hf.norm
  · filter_upwards [] with y
    exact continuous_const.mul
      (continuous_planeFourierCharacter.comp
        (continuous_const.prodMk continuous_id))

/-- Absolute integrability justifying the exchange of spatial and frequency
integrals; the estimate uses only `m ∈ L¹` and `f ∈ L¹`. -/
theorem integrable_inverseSymbol_spatial_frequency {m : Plane → ℝ}
    (hm : Continuous m) (hmi : Integrable m) {f : Plane → ℂ}
    (hf : Integrable f) (x : Plane) :
    Integrable (fun p : Plane × Plane =>
      (m p.1 : ℂ) * planeFourierCharacter (x - p.2) p.1 * f p.2)
      (volume.prod volume) := by
  apply (hmi.norm.mul_prod hf.norm).mono'
  · apply AEStronglyMeasurable.mul
    · exact ((Complex.continuous_ofReal.comp (hm.comp continuous_fst)).mul
        (continuous_planeFourierCharacter.comp
          ((continuous_const.sub continuous_snd).prodMk continuous_fst))).aestronglyMeasurable
    · exact hf.aestronglyMeasurable.comp_snd
  · filter_upwards [] with p
    simp [Complex.norm_real]

/-- Inverse-symbol convolution equals the actual Fourier multiplier integral,
for every spatial point and every integrable input. -/
theorem inverseSymbol_convolution_eq_fourierIntegral {m : Plane → ℝ}
    (hm : Continuous m) (hmi : Integrable m) {f : Plane → ℂ}
    (hf : Integrable f) (x : Plane) :
    (∫ y : Plane, inverseFourierIntegral m (x - y) * f y) =
      ∫ ξ : Plane, (m ξ : ℂ) * planeFourierIntegral f ξ *
        planeFourierCharacter x ξ := by
  calc
    _ = ∫ y : Plane, ∫ ξ : Plane,
        (m ξ : ℂ) * planeFourierCharacter (x - y) ξ * f y := by
      simp only [inverseFourierIntegral, planeFourierCharacter, integral_mul_const]
    _ = ∫ ξ : Plane, ∫ y : Plane,
        (m ξ : ℂ) * planeFourierCharacter (x - y) ξ * f y :=
      (integral_integral_swap (integrable_inverseSymbol_spatial_frequency hm hmi hf x)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp_rw [planeFourierCharacter_sub]
      rw [show (fun y : Plane =>
          (m ξ : ℂ) * (planeFourierCharacter x ξ * planeFourierCharacter (-y) ξ) * f y) =
          (fun y : Plane => ((m ξ : ℂ) * planeFourierCharacter x ξ) *
            (f y * planeFourierCharacter (-y) ξ)) by funext y; ring,
        integral_const_mul]
      simp only [planeFourierIntegral]
      ring

theorem FrequencyCutoff.band_eq_fourierIntegral (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) (x : Plane) :
    L.band k f x = ∫ ξ : Plane, (L.bandSymbol k ξ : ℂ) * planeFourierIntegral f ξ *
      planeFourierCharacter x ξ := by
  exact inverseSymbol_convolution_eq_fourierIntegral (L.bandSymbol_smooth k).continuous
    ((L.bandSymbol_smooth k).continuous.integrable_of_hasCompactSupport
      (L.bandSymbol_compact k)) hf x

/-- The two-dimensional frequency Jacobian for a positive dilation. -/
theorem integral_plane_frequency_rescale (F : Plane → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ ξ : Plane, F ξ) = a ^ 2 • ∫ ξ : Plane, F (a • ξ) := by
  simpa [smul_smul, ha.ne', Plane, Module.finrank_prod] using
    (Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Plane)
      (fun ξ => F (a • ξ)) ha.le)

/-- Rescaling places the actual dyadic symbol on the fixed unit-frequency
annulus; the input Fourier transform is evaluated at the dilated frequency. -/
theorem FrequencyCutoff.band_eq_rescaled_fourierIntegral (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) (x : Plane) :
    L.band k f x = (((2 : ℝ) ^ k) ^ 2) • ∫ ξ : Plane,
      (L.bandSymbol 0 ξ : ℂ) * planeFourierIntegral f ((2 : ℝ) ^ k • ξ) *
        planeFourierCharacter x ((2 : ℝ) ^ k • ξ) := by
  rw [L.band_eq_fourierIntegral k hf x,
    integral_plane_frequency_rescale _ (pow_pos (by norm_num : (0 : ℝ) < 2) k)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [L.bandSymbol_rescale]
  simp [smul_smul]

/-- The real time integral appearing in the frequency representation of a
smoothly localized curve average. -/
def Family.cutoffOscillatoryAmplitude {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (q : Parameters 2 d) (ξ : Plane) : ℂ :=
  ∫ t : ℝ, (χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) ξ

theorem Family.norm_cutoffOscillatoryAmplitude_le {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (q : Parameters 2 d) (ξ : Plane) :
    ‖G.cutoffOscillatoryAmplitude χ q ξ‖ ≤ ∫ t : ℝ, ‖χ (t, q)‖ := by
  calc
    _ ≤ ∫ t : ℝ, ‖(χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) ξ‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp

theorem Family.cutoffOscillatoryIntegrand_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (q : Parameters 2 d) (ξ : Plane) :
    Integrable (fun t : ℝ => (χ (t, q) : ℂ) *
      planeFourierCharacter (G.graphMap q t) ξ) := by
  exact G.cutoffIntegrand_integrable χ hχ hc hγ
    (continuous_planeFourierCharacter.comp (continuous_id.prodMk continuous_const)) q

set_option maxHeartbeats 800000 in
/-- Joint continuity still only requires the geometry on the cutoff support. -/
theorem Family.continuous_cutoffOscillatoryIntegrand {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (q : Parameters 2 d) :
    Continuous (fun p : ℝ × Plane => (χ (p.1, q) : ℂ) *
      planeFourierCharacter (G.graphMap q p.1) p.2) := by
  apply continuous_of_tsupport
  intro p hp
  have he : tsupport (fun p : ℝ × Plane => (χ (p.1, q) : ℂ)) =
      tsupport (fun p : ℝ × Plane => χ (p.1, q)) := by
    unfold tsupport
    congr 1
    ext p
    simp
  have hpχ : (p.1, q) ∈ tsupport χ :=
    tsupport_comp_subset_preimage χ (continuous_fst.prodMk continuous_const)
      (he ▸ tsupport_mul_subset_left hp)
  have hgraph : ContinuousAt (fun p : ℝ × Plane => G.graphMap q p.1) p := by
    exact continuousAt_fst.prodMk ((hγ _ hpχ).comp
      (f := fun p : ℝ × Plane => (p.1, q))
      (continuous_fst.prodMk continuous_const).continuousAt)
  exact ((Complex.continuous_ofReal.comp
    (hχ.comp (continuous_fst.prodMk continuous_const))).continuousAt).mul
      (continuous_planeFourierCharacter.continuousAt.comp
        (hgraph.prodMk continuousAt_snd))

/-- Product-space absolute integrability for the time-frequency exchange. -/
theorem Family.integrable_cutoffOscillatoryProduct {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℂ} (ha : Integrable a) (q : Parameters 2 d) :
    Integrable (fun p : ℝ × Plane =>
      ((χ (p.1, q) : ℂ) * planeFourierCharacter (G.graphMap q p.1) p.2) * a p.2)
      (volume.prod volume) := by
  have hslice : Integrable (fun t : ℝ => χ (t, q)) :=
    (hχ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (cutoffSlice_hasCompactSupport χ hc q)
  apply (hslice.norm.mul_prod ha.norm).mono'
  · exact (G.continuous_cutoffOscillatoryIntegrand χ hχ hγ q).aestronglyMeasurable.mul
      ha.aestronglyMeasurable.comp_snd
  · filter_upwards [] with p
    simp [Complex.norm_real]

theorem Family.cutoffOscillatoryAmplitude_mul_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℂ} (ha : Integrable a) (q : Parameters 2 d) :
    Integrable (fun ξ : Plane => a ξ * G.cutoffOscillatoryAmplitude χ q ξ) := by
  have hi := (G.integrable_cutoffOscillatoryProduct χ hχ hc hγ ha q).integral_prod_right
  apply hi.congr
  filter_upwards [] with ξ
  simp only [integral_mul_const, Family.cutoffOscillatoryAmplitude]
  ring

/-- An actual Fubini identity for every integrable frequency amplitude. -/
theorem Family.cutoffAverage_fourierIntegral_eq {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {a : Plane → ℂ} (ha : Integrable a) (q : Parameters 2 d) :
    G.cutoffAverage χ (fun x => ∫ ξ : Plane, a ξ * planeFourierCharacter x ξ) q =
      ∫ ξ : Plane, a ξ * G.cutoffOscillatoryAmplitude χ q ξ := by
  calc
    _ = ∫ t : ℝ, ∫ ξ : Plane,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) ξ) * a ξ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      ring
    _ = ∫ ξ : Plane, ∫ t : ℝ,
        ((χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) ξ) * a ξ :=
      integral_integral_swap (G.integrable_cutoffOscillatoryProduct χ hχ hc hγ ha q)
    _ = _ := by
      simp only [integral_mul_const, Family.cutoffOscillatoryAmplitude]
      apply integral_congr_ae
      filter_upwards [] with ξ
      ring

theorem FrequencyCutoff.bandFrequencyData_integrable (L : FrequencyCutoff) (k : ℕ)
    {f : Plane → ℂ} (hf : Integrable f) :
    Integrable (fun ξ : Plane => (L.bandSymbol k ξ : ℂ) * planeFourierIntegral f ξ) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp (L.bandSymbol_smooth k).continuous).mul
      (continuous_planeFourierIntegral hf)
  · exact ((L.bandSymbol_compact k).comp_left (g := Complex.ofRealCLM) rfl).mul_right

/-- The actual localized frequency band average, with all integral exchanges
proved for `L¹` inputs and geometry continuous only on the cutoff support. -/
theorem Family.cutoffAverage_band_eq_oscillatoryIntegral {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Integrable f) (k : ℕ) (q : Parameters 2 d) :
    G.cutoffAverage χ (L.band k f) q = ∫ ξ : Plane,
      (L.bandSymbol k ξ : ℂ) * planeFourierIntegral f ξ *
        G.cutoffOscillatoryAmplitude χ q ξ := by
  have he : L.band k f = fun x => ∫ ξ : Plane,
      ((L.bandSymbol k ξ : ℂ) * planeFourierIntegral f ξ) *
        planeFourierCharacter x ξ := funext (L.band_eq_fourierIntegral k hf)
  rw [he]
  exact G.cutoffAverage_fourierIntegral_eq χ hχ hc hγ
    (L.bandFrequencyData_integrable k hf) q

theorem Family.cutoffAverage_band_eq_rescaled_oscillatoryIntegral {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (L : FrequencyCutoff) (hχ : Continuous χ)
    (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Integrable f) (k : ℕ) (q : Parameters 2 d) :
    G.cutoffAverage χ (L.band k f) q = (((2 : ℝ) ^ k) ^ 2) • ∫ ξ : Plane,
      (L.bandSymbol 0 ξ : ℂ) * planeFourierIntegral f ((2 : ℝ) ^ k • ξ) *
        G.cutoffOscillatoryAmplitude χ q ((2 : ℝ) ^ k • ξ) := by
  rw [G.cutoffAverage_band_eq_oscillatoryIntegral χ L hχ hc hγ hf k q,
    integral_plane_frequency_rescale _ (pow_pos (by norm_num : (0 : ℝ) < 2) k)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [L.bandSymbol_rescale]
  simp [smul_smul]

end PlanarNikodym
