import PlanarNikodym.Analysis.Fourier.E3SmoothScalarMainSmoothing
import PlanarNikodym.Analysis.Fourier.GlyzSmoothMovingAtlas
import PlanarNikodym.Analysis.Fourier.ScaledConvolutionRegularity
import PlanarNikodym.Analysis.Jets.ScalarJetWeightedError
import PlanarNikodym.Analysis.Jets.ScalarJetLocalGeometry
import PlanarNikodym.Analysis.Maximal.MaximalMeasurability

/-! Actual scalar local smoothing for every normalized vertical frequency
weight. The nonstationary error, signed cutoffs and fixed time translation
are handled before the final dyadic operator estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym
set_option maxHeartbeats 1200000

/-- A nonnegative cutoff in the standard time window, with the actual
weighted band symbol and no remaining error term. -/
theorem Family.exists_e3_nonnegative_centered_scalar_weighted_smoothing {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (ht : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution
        (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f)) p volume ≤
      ENNReal.ofReal (C * r ^ (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε)) *
        eLpNorm f p volume := by
  let a : ℝ := -((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε
  have hp1 : (1 : ℝ≥0∞) ≤ p := by
    exact_mod_cast (smoothingThreshold_one_le d).trans hp
  obtain ⟨δ, β, hδ, _, hβ, _, hβz, _, herr⟩ :=
    G.exists_scalarJet_microlocal_error_decay χ hχ hc (fun _ _ => hG.contDiffAt) L
  have hβm : ContDiff ℝ ∞ (fun η : ℝ => η ^ m * β η) :=
    (contDiff_id.pow m).mul hβ
  obtain ⟨C, hC, hmain⟩ := G.exists_e3_two_sided_main_global_smoothing hG hdim χ hχ hc hχ0 hd ht
    L (fun η => η ^ m * β η) hβm p hp hε (half_pos hδ)
    (fun η hη => by rw [hβz η hη.le, mul_zero])
  obtain ⟨N, hN⟩ := exists_nat_ge (-a)
  obtain ⟨D, hD, herror⟩ := herr m p hp1 N
  refine ⟨C + D, add_nonneg hC hD, fun r hr f hf hfp => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x :=
    fun _ _ => hG.continuous.continuousAt
  let ae : Plane → ℝ := fun ξ => ξ.2 ^ m * L.bandSymbol 0 ξ * (1 - β ξ.2)
  have hae : ContDiff ℝ ∞ ae := ((contDiff_snd.pow m).mul (L.bandSymbol_smooth 0)).mul
    (contDiff_const.sub (hβ.comp contDiff_snd))
  have hace : HasCompactSupport ae := (L.bandSymbol_compact 0).mul_left.mul_right
  have hmeas : AEStronglyMeasurable (G.cutoffFrequencyError χ ae r f) volume := by
    have he : G.cutoffAverage χ (scaledFrequencyConvolution ae r f) =
        G.cutoffFrequencyError χ ae r f := by
      funext q
      exact G.scalarJet_scaledFrequencyConvolution_eq_frequencyOperator χ hχ.continuous hc hγ
        hae.continuous hace hf r q
    rw [← he]
    exact (G.continuous_cutoffAverage hχ.continuous hc hγ
      (contDiff_scaledFrequencyConvolution hae hace hr0.ne' hf).continuous).aestronglyMeasurable
  have hdec : G.cutoffAverage χ (scaledFrequencyConvolution
      (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f) =
      G.cutoffPartialExtension χ L (fun η => η ^ m * β η) r f +
      G.cutoffFrequencyError χ ae r f := by
    funext q
    exact G.scalarJet_weighted_main_add_error χ hχ.continuous hc hγ L β hβ.continuous hf m r q
  have hpow : (r⁻¹) ^ N ≤ r ^ a := by
    rw [← Real.rpow_natCast, Real.inv_rpow hr0.le]
    rw [← Real.rpow_neg hr0.le]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  rw [hdec]
  calc
    _ ≤ eLpNorm (G.cutoffPartialExtension χ L (fun η => η ^ m * β η) r f) p volume +
        eLpNorm (G.cutoffFrequencyError χ ae r f) p volume :=
      eLpNorm_add_le
        (G.e3_stronglyMeasurable_cutoffPartialExtension hG χ hχ.continuous hc L
          hβm.continuous hf r).aestronglyMeasurable hmeas hp1
    _ ≤ ENNReal.ofReal (C * r ^ a) * eLpNorm f p volume +
        ENNReal.ofReal (D * (r⁻¹) ^ N) * eLpNorm f p volume :=
      add_le_add (hmain r hr f hf hfp) (herror r hr f hf)
    _ ≤ ENNReal.ofReal (C * r ^ a) * eLpNorm f p volume +
        ENNReal.ofReal (D * r ^ a) * eLpNorm f p volume := by
      gcongr
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hC (Real.rpow_nonneg hr0.le _))
        (mul_nonneg hD (Real.rpow_nonneg hr0.le _)), ← add_mul]

/-- Fixed translation of the time window preserves the physical input
norm and the original weighted average exactly. -/
theorem Family.exists_e3_nonnegative_scalar_weighted_smoothing {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (s : ℝ) (ht : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (s - 1) (s + 1))
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution
        (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f)) p volume ≤
      ENNReal.ofReal (C * r ^ (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε)) *
        eLpNorm f p volume := by
  have hdt : ∀ x ∈ tsupport (scalarJetTimeTranslateCutoff χ s),
      (G.glyzTimeTranslate s).cinematicDet x ≠ 0 := by
    intro x hx
    rw [Family.cinematicDet_glyzTimeTranslate]
    exact hd _ (scalarJetTimeTranslateCutoff_support χ s hx)
  obtain ⟨C, hC, h⟩ := (G.glyzTimeTranslate s).exists_e3_nonnegative_centered_scalar_weighted_smoothing
    (G.contDiff_glyzTimeTranslate hG s) hdim (scalarJetTimeTranslateCutoff χ s) (contDiff_scalarJetTimeTranslateCutoff χ hχ s)
    (hasCompactSupport_scalarJetTimeTranslateCutoff χ hc s) (fun x => hχ0 _)
    hdt
    (scalarJetTimeTranslateCutoff_time_support χ s ht) L p hp hε m
  refine ⟨C, hC, fun r hr f hf hfp => ?_⟩
  have hh := h r hr (glyzTimeTranslateInput f s) (integrable_glyzTimeTranslateInput hf s)
    (memLp_glyzTimeTranslateInput hfp s)
  rw [G.scalarJet_weightedAverage_timeTranslate,
    eLpNorm_scalarJetTimeTranslateInput hfp.aestronglyMeasurable] at hh
  exact hh

/-- Signed cutoffs may be chosen arbitrarily in the same fixed regular
open set. The nonnegative decomposition stays inside that open set. -/
theorem Family.exists_e3_scalar_weighted_smoothing_on_open {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d) {O : Set (ℝ × Parameters 2 d)} (hO : IsOpen O) (s : ℝ)
    (hreg : ∀ x ∈ O,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x ∧
      G.cinematicDet x ≠ 0 ∧ x.1 ∈ Ioo (s - 1) (s + 1))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ O)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : smoothingThreshold d ≤ p)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution
        (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f)) p volume ≤
      ENNReal.ofReal (C * r ^ (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε)) *
        eLpNorm f p volume := by
  obtain ⟨χp, χn, hχp, hcp, hsp, hp0, hχn, hcn, hsn, hn0, heq⟩ :=
    exists_scalarJet_signed_cutoff_decomposition χ hχ hc hO hs
  obtain ⟨Cp, hCp, hpos⟩ := G.exists_e3_nonnegative_scalar_weighted_smoothing hG hdim χp hχp hcp hp0 (fun x hx => (hreg x (hsp hx)).2.1)
    s (fun x hx => (hreg x (hsp hx)).2.2) L p hp hε m
  obtain ⟨Cn, hCn, hneg⟩ := G.exists_e3_nonnegative_scalar_weighted_smoothing hG hdim χn hχn hcn hn0 (fun x hx => (hreg x (hsn hx)).2.1)
    s (fun x hx => (hreg x (hsn hx)).2.2) L p hp hε m
  refine ⟨Cp + Cn, add_nonneg hCp hCn, fun r hr f hf hfp => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hγp : ∀ x ∈ tsupport χp, ContinuousAt (fun x => G.γ x.1 x.2) x :=
    fun _ _ => hG.continuous.continuousAt
  have hγn : ∀ x ∈ tsupport χn, ContinuousAt (fun x => G.γ x.1 x.2) x :=
    fun _ _ => hG.continuous.continuousAt
  have hmf : Continuous (scaledFrequencyConvolution
      (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f) :=
    (contDiff_scaledFrequencyConvolution ((contDiff_snd.pow m).mul (L.bandSymbol_smooth 0))
      (L.bandSymbol_compact 0).mul_left hr0.ne' hf).continuous
  have he : χ = χp - χn := funext heq
  have hp1 : (1 : ℝ≥0∞) ≤ p := by
    exact_mod_cast (smoothingThreshold_one_le d).trans hp
  rw [he, G.cutoffAverage_sub_cutoff χp χn hχp.continuous hχn.continuous hcp hcn hγp hγn hmf]
  calc
    _ ≤ eLpNorm (G.cutoffAverage χp (scaledFrequencyConvolution
          (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f)) p volume +
        eLpNorm (G.cutoffAverage χn (scaledFrequencyConvolution
          (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) r f)) p volume :=
      eLpNorm_sub_le (G.continuous_cutoffAverage hχp.continuous hcp hγp hmf).aestronglyMeasurable
        (G.continuous_cutoffAverage hχn.continuous hcn hγn hmf).aestronglyMeasurable hp1
    _ ≤ _ := by
      have hh := add_le_add (hpos r hr f hf hfp) (hneg r hr f hf hfp)
      simpa only [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCp
        (Real.rpow_nonneg hr0.le _)) (mul_nonneg hCn (Real.rpow_nonneg hr0.le _))] using hh

/-- The scalar estimate used in the actual auxiliary-jet expansion.
The single neighborhood precedes every cutoff and every vertical order. -/
theorem Family.exists_e3_scalar_weighted_smoothing_neighborhood {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (hdim : 1 ≤ d) (x : ℝ × Parameters 2 d)
    (hd : G.cinematicDet x ≠ 0) :
    ∃ O : Set (ℝ × Parameters 2 d), IsOpen O ∧ x ∈ O ∧
      (∀ y ∈ O, ContDiffAt ℝ ∞ (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) y) ∧
      ∀ (χ : Cutoff d), ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∀ (L : FrequencyCutoff) (p : ℝ≥0), smoothingThreshold d ≤ p →
      ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
        eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution
          (fun ξ : Plane => ξ.2 ^ m * L.bandSymbol 0 ξ) ((2 : ℝ) ^ k) f)) p volume ≤
        C * dyadicWeight (-((d + 1 : ℕ) : ℝ) / (p : ℝ) + ε) k * eLpNorm f p volume := by
  let O := {y : ℝ × Parameters 2 d | G.cinematicDet y ≠ 0} ∩
    {y : ℝ × Parameters 2 d | y.1 ∈ Ioo (x.1 - 1) (x.1 + 1)}
  have hO : IsOpen O :=
    ((G.continuous_cinematicDet_of_contDiff hG).isOpen_preimage _ isClosed_singleton.isOpen_compl).inter
      (isOpen_Ioo.preimage continuous_fst)
  have hx : x ∈ O := ⟨hd, by constructor <;> linarith⟩
  have hreg : ∀ y ∈ O, ContDiffAt ℝ ∞ (fun z : ℝ × Parameters 2 d => G.γ z.1 z.2) y ∧
      G.cinematicDet y ≠ 0 ∧ y.1 ∈ Ioo (x.1 - 1) (x.1 + 1) :=
    fun _ hy => ⟨hG.contDiffAt, hy⟩
  refine ⟨O, hO, hx, fun y hy => (hreg y hy).1, ?_⟩
  intro χ hχ hc hs L p hp ε hε m
  obtain ⟨C, hC, h⟩ := G.exists_e3_scalar_weighted_smoothing_on_open hG hdim hO x.1 hreg χ hχ hc hs
    L p hp hε m
  refine ⟨⟨C, hC⟩, fun k f hf hfp => ?_⟩
  have hh := h ((2 : ℝ) ^ k) (one_le_pow₀ (by norm_num)) f hf hfp
  have hw (a : ℝ) : ENNReal.ofReal (((2 : ℝ) ^ k) ^ a) = dyadicWeight a k := by
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow (by positivity)]
    rfl
  rw [ENNReal.ofReal_mul hC, hw] at hh
  convert hh using 1
  rw [ENNReal.ofReal_eq_coe_nnreal hC]
  rfl

end PlanarNikodym
