import PlanarNikodym.Analysis.Fourier.E3SmoothPositiveRadialMainSmoothing
import PlanarNikodym.Analysis.Fourier.E3SmoothPartialMemLp

/-! ENNReal norm versions of actual positive-radial main smoothing.
The compact extension argument proves finiteness before converting norms. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem Family.exists_e3_positive_radial_main_eLp_smoothing {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (hd : 1 ≤ d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (htime : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε κ M Q : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hradial : Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ⊆ Icc κ M)
    (hQ : 0 ≤ Q) :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        ENNReal.ofReal (C * r ^ (-(d + 1 : ℝ) / p + ε)) * eLpNorm f p volume +
        ENNReal.ofReal (C * r ^ (-Q)) * eLpNorm f 1 volume := by
  obtain ⟨C, R, hC, hR, h⟩ := G.exists_e3_positive_radial_main_smoothing hG hd χ hχ hc hχ0
    hdet htime L β hβ hp hε hκ hradial hQ
  refine ⟨C, R, hC, hR, fun r hr f hf hfp => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  exact glyz_eLpNorm_le_of_lpNorm_le
    (G.e3_memLp_cutoffPartialExtension hG χ hχ hc L β hβ hf r p) hfp
    (memLp_one_iff_integrable.mpr hf) (by positivity) (by positivity) (h r hr f hf hfp)

theorem Family.exists_e3_positive_radial_main_eLp_smoothing_nat {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (hd : 1 ≤ d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (htime : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε κ M : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hradial : Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ⊆ Icc κ M)
    (N : ℕ) :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        ENNReal.ofReal (C * r ^ (-(d + 1 : ℝ) / p + ε)) * eLpNorm f p volume +
        ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f 1 volume := by
  obtain ⟨C, R, hC, hR, h⟩ := G.exists_e3_positive_radial_main_eLp_smoothing hG hd χ hχ hc hχ0
    hdet htime L β hβ hp hε hκ hradial (Q := (N : ℝ)) (Nat.cast_nonneg N)
  refine ⟨C, R, hC, hR, fun r hr f hf hfp => ?_⟩
  have hr0 : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  simpa only [Real.rpow_neg hr0.le, Real.rpow_natCast, inv_pow] using h r hr f hf hfp

end PlanarNikodym
