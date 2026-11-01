import PlanarNikodym.Analysis.Fourier.SmoothFullSmallCinematicMainLp
import PlanarNikodym.Analysis.Fourier.FullLinearScaleMainLp

/-! Genuine C-infinity estimates, including zero auxiliary dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators ComplexConjugate
namespace PlanarNikodym

theorem Family.exists_smooth_full_cinematic_linear_scale_main_Lp {d : ℕ}
    (G : Family 2 d) (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)

    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (F : FrequencyCutoff) (βfreq : ℝ → ℝ) (hβfreq : ContDiff ℝ ∞ βfreq)
    {p : ℝ≥0} (hp : 2 ≤ p) {κ : ℝ} (hκ : 0 < κ)
    (hgap : ∀ ξ : Plane, |ξ.2| < κ → F.bandSymbol 0 ξ * βfreq ξ.2 = 0) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ (b : ℝ) (N : ℕ) (f : Plane → ℂ),
      Integrable f → MemLp f p volume → ∀ r : ℝ, R ≤ r →
      eLpNorm (G.fullFiniteSliceMain χ F βfreq r b (2 * Real.pi * r)⁻¹ N f) p
        (fullFiniteSliceMainMeasure d N) ≤
        ENNReal.ofReal (C * r ^ (-1 + 1 / (p : ℝ))) * eLpNorm f p volume := by
  obtain ⟨C, ε, hC, hε, hb⟩ :=
    G.exists_smooth_full_cinematic_small_main_Lp hG χ hχ hc hχ0 hdet F βfreq hβfreq hp
  obtain ⟨R, hR, hscale⟩ := exists_Fourier_criticalTimeScale_threshold 0
    (show 0 < ε / 2 by positivity)
  have hp0 : (0 : ℝ) < p := (by norm_num : (0 : ℝ) < 2).trans_le hp
  let A := (2 * Real.pi * κ⁻¹) ^ (1 / (p : ℝ)) * (2 * Real.pi) ^ (-1 + 1 / (p : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C * A, R, mul_nonneg hC hA, hR, ?_⟩
  intro b N f hf hfp r hr
  have hr0 : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  obtain ⟨hδ, hδbound, _⟩ := hscale r hr
  have he : criticalTimeScale 0 (2 * Real.pi * r) = (2 * Real.pi * r)⁻¹ := by
    simp only [criticalTimeScale, Nat.reduceAdd, Nat.cast_one, div_one, Real.rpow_neg_one]
  rw [he] at hδ hδbound
  have hα : (2 * Real.pi * r) * ((2 * Real.pi * r)⁻¹) ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1 := by
    have hval : (2 * Real.pi * r) * ((2 * Real.pi * r)⁻¹) ^ (2 : ℕ) = (2 * Real.pi * r)⁻¹ := by
      field_simp
    rw [hval]
    exact ⟨hδ.le, hδbound.trans (min_le_left _ _)⟩
  have hh := hb b (2 * Real.pi * r)⁻¹ N f hf hfp κ r hκ hr0 hδ
    (hδbound.trans (min_le_left _ _)) (hδbound.trans (min_le_right _ _)) hα hgap
  rw [linear_main_interpolation_scale_eq hκ hr0 hp0] at hh
  simpa only [A, mul_assoc] using hh

end PlanarNikodym
