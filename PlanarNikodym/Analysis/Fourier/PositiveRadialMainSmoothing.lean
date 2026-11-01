import PlanarNikodym.Analysis.Fourier.GlyzPartialDecouplingTransfer
import PlanarNikodym.Analysis.Fourier.GlyzPartialSmoothingAlgebra
import PlanarNikodym.Analysis.Fourier.FullCinematicMainLpDecay

/-! Actual positive-radial main smoothing: the proven successive
lower-degree decoupling and the proven full-parameter smallest-piece
endpoint are combined with the original compact Fourier data. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 1200000 in
theorem Family.exists_positive_radial_main_smoothing {d : ℕ} (G : Family 2 d)
    (hd : 1 ≤ d) (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (htime : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε κ M Q : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hradial : Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ⊆ Icc κ M)
    (hQ : 0 ≤ Q) :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      lpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        C * r ^ (-(d + 1 : ℝ) / p + ε) * lpNorm f p volume +
        C * r ^ (-Q) * lpNorm f 1 volume := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.continuous.comp continuous_snd)
  have hmc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  obtain ⟨ρ, hρs, hρc, hρ⟩ := exists_partialData_radial_cutoff hmc
  let a := partialDataAmplitude χ ρ
  have has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ tsupport χ := by
    intro x t η hn
    apply subset_tsupport
    intro hz
    exact hn (by simp [a, partialDataAmplitude, hz])
  have hp2 : (2 : ℝ≥0) < p := by
    have hcR : glyzCriticalExponent (d + 1) ≤ (p : ℝ) := hp
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [glyzCriticalExponent] at hcR
    push_cast at hcR
    have hh : (2 : ℝ) < p := by nlinarith
    exact hh
  have hp0 : 0 < p := (by norm_num : (0 : ℝ≥0) < 2).trans hp2
  have hgap : ∀ ξ : Plane, |ξ.2| < κ → L.bandSymbol 0 ξ * β ξ.2 = 0 := by
    intro ξ hξ
    by_contra hn
    have hη := hradial ⟨ξ, subset_tsupport m hn, rfl⟩
    linarith [hη.1, le_abs_self ξ.2]
  obtain ⟨D, R, hD, hR, hend⟩ := G.exists_full_cinematic_critical_main_Lp_decay
    χ hχ hc hχ0 ha hdet L β hβ hp2 hκ hgap
  obtain ⟨C₀, hC₀, hdec⟩ := G.glyz_cascade_decoupling hd hc.isCompact
    (isOpen_analyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) ha
    (fun x hx => hx.contDiffAt) (contDiff_partialDataAmplitude hχ hρs)
    (hasCompactSupport_partialDataAmplitude hc hρc) hdet has htime hp hε hκ
    (show 0 ≤ Q + 2 by linarith) (rmax := M)
  let α : ℝ := 1 / 2 - (d + 1 : ℝ) / p + ε
  let V : ℝ := 2 * lpNorm m 1 volume
  let C : ℝ := C₀ * ((2 * Real.pi) ^ α * D + (2 * Real.pi) ^ (-(Q + 2)) * V) + 1
  have hV : 0 ≤ V := mul_nonneg (by norm_num) lpNorm_nonneg
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, R, hC, hR, fun r hr f hf hfp => ?_⟩
  have hr1 : 1 ≤ r := hR.trans hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have hcpi : 0 < 2 * Real.pi := by positivity
  have hΛ : 1 ≤ 2 * Real.pi * r := by nlinarith [Real.pi_gt_three]
  let δ : ℝ := (2 * Real.pi * r) ^ (-(1 / (2 : ℝ)))
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  let g := timeRestrictedPartialData (Icc (-1 : ℝ) 1) m f r
  have hg : Integrable g := integrable_timeRestrictedPartialData measurableSet_Icc
    isCompact_Icc.measure_lt_top.ne hm hmc hf r
  have hgs : Function.support g ⊆ {y | y.2 ∈ Icc κ M} :=
    timeRestrictedPartialData_radial_support hradial f r
  have hrawdec := hdec (2 * Real.pi * r) hΛ g hg hgs
  have htransfer := G.glyz_partial_decoupling_transfer χ hχ hc ha
    (fun x hx => ⟨(htime x hx).1.le, (htime x hx).2.le⟩) L β hβ ρ hρs hρc hρ
    hp0 hf r hδ (glyzExactTimeCount δ) hrawdec
  have he := hend (-1) (glyzExactTimeCount δ) f hf hfp r hr
  change eLpNorm (G.fullFiniteSliceMain χ L β r (-1) δ (glyzExactTimeCount δ) f) p
      (fullFiniteSliceMainMeasure d (glyzExactTimeCount δ)) ≤
    ENNReal.ofReal (D * r ^ (-(1 / 2 : ℝ))) * eLpNorm f p volume at he
  have hfinite : ENNReal.ofReal (D * r ^ (-(1 / 2 : ℝ))) * eLpNorm f p volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfp.eLpNorm_ne_top
  have heR := ENNReal.toReal_mono hfinite he
  rw [toReal_eLpNorm (G.measurable_fullFiniteSliceMain χ hχ.continuous hc ha L β
      hβ.continuous r (-1) δ (glyzExactTimeCount δ) hf).aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    toReal_eLpNorm hfp.aestronglyMeasurable] at heR
  have hmass := integral_norm_timeRestrictedPartialData_le (T := Icc (-1 : ℝ) 1) measurableSet_Icc
    isCompact_Icc.measure_lt_top.ne hm hmc hf r
  norm_num [Real.volume_Icc] at hmass
  have hh := glyz_partial_smoothing_combine hcpi hC₀.le hD hV hr0
    (show 0 ≤ lpNorm f p volume from lpNorm_nonneg)
    (show 0 ≤ lpNorm f 1 volume from lpNorm_nonneg) htransfer heR hmass
  have hexp : α + (-(1 / 2 : ℝ)) = -(d + 1 : ℝ) / p + ε := by dsimp [α]; ring
  dsimp only [α] at hexp
  simpa only [hexp] using hh

end PlanarNikodym
