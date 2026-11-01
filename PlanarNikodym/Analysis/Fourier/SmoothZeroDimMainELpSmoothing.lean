import PlanarNikodym.Analysis.Fourier.SmoothZeroDimMainSmoothing
import PlanarNikodym.Analysis.Fourier.E3SmoothPartialMemLp

/-! Genuine C-infinity estimates, including zero auxiliary dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators ComplexConjugate
namespace PlanarNikodym

theorem Family.exists_smooth_zero_dim_positive_main_eLp_smoothing
    (G : Family 2 0) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 0 => G.γ x.1 x.2)) (χ : Cutoff 0) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)

    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (htime : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {p : ℝ≥0} (hp : 2 ≤ p) {ε κ M Q : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hradial : Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ⊆ Icc κ M)
    (hQ : 0 ≤ Q) :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        ENNReal.ofReal (C * r ^ (-(1 / (p : ℝ)) + ε)) * eLpNorm f p volume +
        ENNReal.ofReal (C * r ^ (-Q)) * eLpNorm f 1 volume := by
  obtain ⟨C, R, hC, hR, hb⟩ := G.exists_smooth_zero_dim_positive_main_smoothing
    hG χ hχ hc hχ0 hdet htime L β hβ hp hε hκ hradial hQ
  refine ⟨C, R, hC, hR, ?_⟩
  intro r hr f hf hfp
  have hmain := G.e3_memLp_cutoffPartialExtension hG χ hχ hc L β hβ hf r (p : ℝ≥0∞)
  have hr0 : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  have hA : 0 ≤ C * r ^ (-(1 / (p : ℝ)) + ε) := mul_nonneg hC.le (Real.rpow_nonneg hr0.le _)
  have hB : 0 ≤ C * r ^ (-Q) := mul_nonneg hC.le (Real.rpow_nonneg hr0.le _)
  exact glyz_eLpNorm_le_of_lpNorm_le hmain hfp (memLp_one_iff_integrable.mpr hf)
    hA hB (hb r hr f hf hfp)

/-- Natural-order remainder interface for the final all-dimensional assembly. -/
theorem Family.exists_smooth_zero_dim_positive_main_eLp_smoothing_nat
    (G : Family 2 0) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 0 => G.γ x.1 x.2)) (χ : Cutoff 0) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)

    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (htime : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {p : ℝ≥0} (hp : 2 ≤ p) {ε κ M : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hradial : Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ⊆ Icc κ M)
    (N : ℕ) :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        ENNReal.ofReal (C * r ^ (-(1 / (p : ℝ)) + ε)) * eLpNorm f p volume +
        ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f 1 volume := by
  obtain ⟨C, R, hC, hR, hb⟩ := G.exists_smooth_zero_dim_positive_main_eLp_smoothing
    hG χ hχ hc hχ0 hdet htime L β hβ hp hε hκ hradial (Nat.cast_nonneg N)
  refine ⟨C, R, hC, hR, ?_⟩
  intro r hr f hf hfp
  have hh := hb r hr f hf hfp
  have hr0 : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  rw [Real.rpow_neg hr0.le, Real.rpow_natCast, ← inv_pow] at hh
  exact hh

end PlanarNikodym
