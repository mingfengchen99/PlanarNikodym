import PlanarNikodym.Analysis.Fourier.GlyzPartialDecouplingTransfer

/-! Finiteness of the actual partial Fourier extension and a safe transfer
from real norms to ENNReal norms. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 800000 in
theorem Family.memLp_cutoffPartialExtension {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ha : ∀ x ∈ tsupport χ, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) (p : ℝ≥0∞) :
    MemLp (G.cutoffPartialExtension χ L β r f) p volume := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.continuous.comp continuous_snd)
  have hmc : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  obtain ⟨ρ, hρs, hρc, hρ⟩ := exists_partialData_radial_cutoff hmc
  let T := Prod.fst '' tsupport χ
  have hTc : IsCompact T := hc.isCompact.image continuous_fst
  have hT : ∀ x ∈ tsupport χ, x.1 ∈ T := fun x hx => ⟨x, hx, rfl⟩
  let g := timeRestrictedPartialData T m f r
  have hg : Integrable g := integrable_timeRestrictedPartialData hTc.measurableSet
    hTc.measure_lt_top.ne hm hmc hf r
  let a := partialDataAmplitude χ ρ
  have has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ tsupport χ := by
    intro x t η hn
    apply subset_tsupport
    intro hz
    exact hn (by simp [a, partialDataAmplitude, hz])
  obtain ⟨H, _, _, hH, _, heq⟩ := G.exists_glyz_global_smooth_phase hc.isCompact
    (isOpen_analyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) ha
    (fun x hx => hx.contDiffAt)
  have ha' : ContDiff ℝ ∞ a := contDiff_partialDataAmplitude hχ hρs
  have hac : HasCompactSupport a := hasCompactSupport_partialDataAmplitude hc hρc
  have hΦH : ContDiff ℝ ∞ (fun x : Parameters 2 d × ℝ => H.γ x.2 x.1) :=
    hH.comp (contDiff_snd.prodMk contDiff_fst)
  have hraw := memLp_glyzRawExtension volume hΦH ha' hac hg (2 * Real.pi * r) p
  rw [heq a has g (2 * Real.pi * r)] at hraw
  have hparent : G.cutoffPartialExtension χ L β r f =
      r ^ 2 • glyzRawExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a g
        (2 * Real.pi * r) := by
    funext x
    exact G.cutoffPartialExtension_eq_raw_compact_amplitude χ L β T hT ρ hρ r f x
  rw [hparent]
  exact hraw.const_smul _

theorem glyz_eLpNorm_le_of_lpNorm_le {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {u : X → ℂ} {f : Y → ℂ} {p : ℝ≥0∞} {A B : ℝ}
    (hu : MemLp u p μ) (hfp : MemLp f p ν) (hf1 : MemLp f 1 ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : lpNorm u p μ ≤ A * lpNorm f p ν + B * lpNorm f 1 ν) :
    eLpNorm u p μ ≤ ENNReal.ofReal A * eLpNorm f p ν +
      ENNReal.ofReal B * eLpNorm f 1 ν := by
  have hh := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_add (mul_nonneg hA lpNorm_nonneg) (mul_nonneg hB lpNorm_nonneg),
    ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB,
    ofReal_lpNorm hu, ofReal_lpNorm hfp, ofReal_lpNorm hf1] at hh
  exact hh

end PlanarNikodym
