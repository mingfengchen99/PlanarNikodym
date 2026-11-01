import PlanarNikodym.Analysis.Fourier.GlyzLocalExactScaleL1Decoupling
import PlanarNikodym.Analysis.Fourier.FullLinearScaleMainLp
import PlanarNikodym.Analysis.Fourier.GlyzPartialDecouplingTransfer
import PlanarNikodym.Analysis.Fourier.GlyzPartialSmoothingAlgebra

/-! The actual positive-radial main smoothing estimate in d=0.
Single-degree decoupling at inverse frequency combines with the full
small-scale endpoint, including p=2, with an arbitrary L1 remainder. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in
theorem Family.exists_zero_dim_positive_main_smoothing
    (G : Family 2 0) (χ : Cutoff 0) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun y : ℝ × Parameters 2 0 => G.γ y.1 y.2) x)
    (hdet : ∀ x ∈ tsupport χ, G.cinematicDet x ≠ 0)
    (htime : ∀ x ∈ tsupport χ, x.1 ∈ Ioo (-1 : ℝ) 1)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {p : ℝ≥0} (hp : 2 ≤ p) {ε κ M Q : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hradial : Prod.snd '' tsupport (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) ⊆ Icc κ M)
    (hQ : 0 ≤ Q) :
    ∃ C R : ℝ, 0 < C ∧ 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      ∀ f : Plane → ℂ, Integrable f → MemLp f p volume →
      lpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        C * r ^ (-(1 / (p : ℝ)) + ε) * lpNorm f p volume +
        C * r ^ (-Q) * lpNorm f 1 volume := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.continuous.comp continuous_snd)
  have hmc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  obtain ⟨ρ, hρ, hcρ, hρ1⟩ := exists_partialData_radial_cutoff hmc
  let a := partialDataAmplitude χ ρ
  have ha' : ContDiff ℝ ∞ a := contDiff_partialDataAmplitude hχ hρ
  have hac : HasCompactSupport a := hasCompactSupport_partialDataAmplitude hc hcρ
  have has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ tsupport χ := by
    intro x t η hn
    apply subset_tsupport
    intro hz
    exact hn (by simp [a, partialDataAmplitude, hz])
  have hpcrit : glyzCriticalNNExponent (0 + 1) ≤ p := by
    have he : glyzCriticalNNExponent 1 = (2 : ℝ≥0) := by
      apply Subtype.ext
      norm_num [glyzCriticalNNExponent, glyzCriticalExponent]
      rfl
    simpa only [Nat.zero_add, he] using hp
  obtain ⟨C, hC, hdec⟩ := G.glyz_local_exact_scale_decoupling_L1 hc.isCompact
    (isOpen_analyticAt ℝ (fun x : ℝ × Parameters 2 0 => G.γ x.1 x.2)) ha
    (fun x hx => hx.contDiffAt) ha' hac hdet has htime hpcrit hε hκ
    (show 0 ≤ Q + 2 by linarith) (rmax := M)
  have hgap (ξ : Plane) (hξ : |ξ.2| < κ) : L.bandSymbol 0 ξ * β ξ.2 = 0 := by
    by_contra hn
    have hh := (hradial ⟨ξ, subset_tsupport m hn, rfl⟩).1
    exact (not_lt_of_ge hh) ((le_abs_self ξ.2).trans_lt hξ)
  obtain ⟨D, R, hD, hR, hend⟩ :=
    G.exists_full_cinematic_linear_scale_main_Lp χ hχ hc hχ0 ha hdet L β hβ hp hκ hgap
  let V := (volume (Icc (-1 : ℝ) 1)).toReal * lpNorm m 1 volume
  have hV : 0 ≤ V := mul_nonneg ENNReal.toReal_nonneg lpNorm_nonneg
  let α := 1 - 2 / (p : ℝ) + ε
  let K := C * ((2 * Real.pi) ^ α * D + (2 * Real.pi) ^ (-(Q + 2)) * V) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hp0 : 0 < p := (by norm_num : (0 : ℝ≥0) < 2).trans_le hp
  have hpexp : coneDecouplingExponent (0 + 1) (p : ℝ) + ε = α := by
    dsimp [coneDecouplingExponent, α]
    norm_num
    ring
  refine ⟨K, R, hK, hR, ?_⟩
  intro r hr f hf hfp
  let Λ := 2 * Real.pi * r
  let δ := Λ ^ (-(1 / (((0 : ℕ) : ℝ) + 1)))
  let g := timeRestrictedPartialData (Icc (-1 : ℝ) 1) m f r
  let N := glyzExactTimeCount δ
  have hr0 : 0 < r := zero_lt_one.trans_le (hR.trans hr)
  have hΛ : 1 ≤ Λ := by dsimp [Λ]; nlinarith [Real.pi_gt_three, hR.trans hr]
  have heδ : δ = (2 * Real.pi * r)⁻¹ := by
    dsimp [δ, Λ]
    norm_num [Real.rpow_neg_one]
  have hδ : 0 < δ := by rw [heδ]; positivity
  have hg : Integrable g := integrable_timeRestrictedPartialData measurableSet_Icc
    isCompact_Icc.measure_lt_top.ne hm hmc hf r
  have hgs : Function.support g ⊆ {y | y.2 ∈ Icc κ M} :=
    timeRestrictedPartialData_radial_support hradial f r
  have hd := hdec Λ hΛ g hg hgs
  dsimp only at hd
  rw [hpexp] at hd
  have hx := G.glyz_partial_decoupling_transfer χ hχ hc ha
    (fun x hx => ⟨(htime x hx).1.le, (htime x hx).2.le⟩) L β hβ
    ρ hρ hcρ hρ1 hp0 hf r hδ N (C := C) (α := α) (Q := Q + 2) (by
      dsimp only [a, g, m, Λ, δ, N] at hd ⊢
      exact hd)
  have hy : lpNorm (G.fullFiniteSliceMain χ L β r (-1) δ N f) p
      (fullFiniteSliceMainMeasure 0 N) ≤ D * r ^ (-1 + 1 / (p : ℝ)) * lpNorm f p volume := by
    have hh := hend (-1) N f hf hfp r hr
    have hfin : ENNReal.ofReal (D * r ^ (-1 + 1 / (p : ℝ))) * eLpNorm f p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfp.eLpNorm_ne_top
    have ht := ENNReal.toReal_mono hfin hh
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hD (Real.rpow_nonneg hr0.le _)),
      toReal_eLpNorm hfp.aestronglyMeasurable,
      toReal_eLpNorm (G.measurable_fullFiniteSliceMain χ hχ.continuous hc ha L β
        hβ.continuous r (-1) (2 * Real.pi * r)⁻¹ N hf).aestronglyMeasurable] at ht
    simpa only [heδ] using ht
  have hmass : (∫ y, ‖g y‖) ≤ V * lpNorm f 1 volume :=
    integral_norm_timeRestrictedPartialData_le measurableSet_Icc isCompact_Icc.measure_lt_top.ne hm hmc hf r
  have hfinal := glyz_partial_smoothing_combine (by positivity : 0 < 2 * Real.pi)
    hC.le hD hV hr0 lpNorm_nonneg lpNorm_nonneg hx hy hmass
  have he : α + (-1 + 1 / (p : ℝ)) = -(1 / (p : ℝ)) + ε := by dsimp [α]; ring
  simpa only [he] using hfinal

end PlanarNikodym
