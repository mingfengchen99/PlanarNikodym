import PlanarNikodym.Analysis.Fourier.CinematicPartialL2
import PlanarNikodym.Analysis.Fourier.ScaledConvolutionRegularity
import PlanarNikodym.Analysis.Fourier.E3SmoothPartialMeasurability
import PlanarNikodym.Analysis.Jets.ScalarJetWeightedError
import PlanarNikodym.Analysis.Maximal.MaximalMeasurability

/-! The sharp L2 gain for every normalized vertical multiplier of the
original average, including its off-cone error. These scalar estimates
supply the actual finite auxiliary-jet expansion. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym

theorem Family.exists_cinematic_scalar_weighted_L2 {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ,
      Integrable f → MemLp f 2 volume →
      eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution
        (fun ξ : Plane => ξ.2^m*L.bandSymbol 0 ξ) r f)) 2 volume ≤
        ENNReal.ofReal C * ENNReal.ofReal (r^(-(1/2 : ℝ))) * eLpNorm f 2 volume := by
  obtain ⟨δ,β,hδ,_hβδ,hβ,_hβc,hβz,_hβ1,herr⟩ :=
    G.exists_scalarJet_microlocal_error_decay χ hχ hc (fun _ _ => hG.contDiffAt) L
  have hβm : ContDiff ℝ ∞ (fun η : ℝ => η^m*β η) := (contDiff_id.pow m).mul hβ
  obtain ⟨C,hC,hmain⟩ := G.exists_cinematic_partial_main_L2 hG χ hχ hc hd L
    (fun η => η^m*β η) hβm (half_pos hδ)
    (fun η hη => by rw [hβz η hη.le,mul_zero])
  obtain ⟨D,hD,herror⟩ := herr m 2 (by norm_num) 1
  refine ⟨C.toReal+D,add_nonneg ENNReal.toReal_nonneg hD,?_⟩
  intro r hr f hf hf2
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x :=
    fun _ _ => hG.continuous.continuousAt
  let ae : Plane → ℝ := fun ξ => ξ.2^m*L.bandSymbol 0 ξ*(1-β ξ.2)
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
      (fun ξ : Plane => ξ.2^m*L.bandSymbol 0 ξ) r f) =
      G.cutoffPartialExtension χ L (fun η => η^m*β η) r f +
      G.cutoffFrequencyError χ ae r f := by
    funext q
    exact G.scalarJet_weighted_main_add_error χ hχ.continuous hc hγ L β hβ.continuous hf m r q
  have hpow : (r⁻¹)^1 ≤ r^(-(1/2 : ℝ)) := by
    rw [pow_one,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  rw [hdec]
  calc
    _ ≤ eLpNorm (G.cutoffPartialExtension χ L (fun η => η^m*β η) r f) 2 volume +
        eLpNorm (G.cutoffFrequencyError χ ae r f) 2 volume :=
      eLpNorm_add_le
        (G.e3_stronglyMeasurable_cutoffPartialExtension hG χ hχ.continuous hc L
          hβm.continuous hf r).aestronglyMeasurable hmeas (by norm_num)
    _ ≤ C * ENNReal.ofReal (r^(-(1/2 : ℝ))) * eLpNorm f 2 volume +
        ENNReal.ofReal (D*(r⁻¹)^1) * eLpNorm f 2 volume :=
      add_le_add (hmain r hr0 f hf hf2) (herror r hr f hf)
    _ ≤ C * ENNReal.ofReal (r^(-(1/2 : ℝ))) * eLpNorm f 2 volume +
        ENNReal.ofReal (D*r^(-(1/2 : ℝ))) * eLpNorm f 2 volume := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul hD,← ENNReal.ofReal_toReal hC,← add_mul,← add_mul,
        ← ENNReal.ofReal_add ENNReal.toReal_nonneg hD]
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

theorem Family.exists_cinematic_scalar_weighted_dyadic_L2 {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hd : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (L : FrequencyCutoff) (m : ℕ) :
    ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f 2 volume →
      eLpNorm (G.cutoffAverage χ (scaledFrequencyConvolution
        (fun ξ : Plane => ξ.2^m*L.bandSymbol 0 ξ) ((2 : ℝ)^k) f)) 2 volume ≤
        C * dyadicWeight (-(1/2 : ℝ)) k * eLpNorm f 2 volume := by
  obtain ⟨C,hC,h⟩ := G.exists_cinematic_scalar_weighted_L2 hG χ hχ hc hd L m
  refine ⟨⟨C,hC⟩,?_⟩
  intro k f hf hf2
  have hh := h ((2 : ℝ)^k) (one_le_pow₀ (by norm_num)) f hf hf2
  have hw (a : ℝ) : ENNReal.ofReal (((2 : ℝ)^k)^a) = dyadicWeight a k := by
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_pow (by positivity)]
    rfl
  rw [hw] at hh
  convert hh using 1
  rw [ENNReal.ofReal_eq_coe_nnreal hC]
  rfl

end PlanarNikodym
