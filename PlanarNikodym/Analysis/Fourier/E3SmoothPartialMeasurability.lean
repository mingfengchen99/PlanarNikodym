import PlanarNikodym.Analysis.Fourier.FullCinematicMainLpTransport

/-! Actual partial extension and finite time-slice measurability for
C∞ phases, without replacing smoothness by analyticity. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace PlanarNikodym

theorem Family.e3_stronglyMeasurable_cutoffPartialExtension {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : Continuous χ) (_hc : HasCompactSupport χ)
    (L : FrequencyCutoff) {β : ℝ → ℝ} (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    StronglyMeasurable (G.cutoffPartialExtension χ L β r f) := by
  let Φ : ℝ × Parameters 2 d → ℝ := fun x => G.γ x.1 x.2
  let Ψ := Φ
  have hΨ : ContDiff ℝ ∞ Ψ := hG
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : Continuous m := (L.bandSymbol_smooth 0).continuous.mul (hβ.comp continuous_snd)
  let A := fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)
  have hA : Continuous A := weighted_scaledFourierData_continuous hm hf r
  let H : (Parameters 2 d × ℝ) × ℝ → ℂ := fun x =>
    (χ (x.2, x.1.1) : ℂ) * partialFourierData A r x.2 x.1.2 *
      oneDimFourierCharacter r (Ψ (x.2, x.1.1)) x.1.2
  have hphase : Continuous (fun x : (Parameters 2 d × ℝ) × ℝ =>
      oneDimFourierCharacter r (Ψ (x.2, x.1.1)) x.1.2) := by
    unfold oneDimFourierCharacter
    have hReal : Continuous (fun x : (Parameters 2 d × ℝ) × ℝ =>
        2 * Real.pi * r * Ψ (x.2, x.1.1) * x.1.2) :=
      (continuous_const.mul (hΨ.continuous.comp (continuous_snd.prodMk continuous_fst.fst))).mul
        continuous_fst.snd
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hReal).mul continuous_const)
  have hH : StronglyMeasurable H :=
    ((Complex.continuous_ofReal.comp (hχ.comp (continuous_snd.prodMk continuous_fst.fst))).stronglyMeasurable.mul
      ((stronglyMeasurable_partialFourierData hA r).comp_measurable
        (measurable_snd.prodMk measurable_fst.snd))).mul hphase.stronglyMeasurable
  have hInt : StronglyMeasurable (fun q : Parameters 2 d => ∫ η : ℝ, ∫ t : ℝ, H ((q, η), t)) :=
    (hH.integral_prod_right' (ν := volume)).integral_prod_right' (ν := volume)
  have hres : StronglyMeasurable (fun q => r ^ 2 • ∫ η, ∫ t, H ((q, η), t)) :=
    hInt.const_smul (r ^ 2)
  convert hres using 1
  rfl


theorem Family.e3_measurable_finiteSliceMain {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) (q : Aux 2 → Parameters 2 d) (hq : Measurable q)
    {f : Plane → ℂ} (hf : Integrable f) :
    Measurable (G.finiteSliceMain χ L β r b δ N q f) := by
  apply measurable_from_prod_countable_right
  intro j
  have hj : Continuous (scaleTimeLocalizedCutoff χ b δ j.val) :=
    hχ.mul ((contDiff_scaleTimeCutoff b δ j.val).continuous.comp continuous_fst)
  exact (G.e3_stronglyMeasurable_cutoffPartialExtension hG _ hj
    (hasCompactSupport_scaleTimeLocalizedCutoff hc b δ j.val)
    L hβ hf r).measurable.comp hq

theorem Family.e3_lintegral_finiteSliceMain {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) (q : Aux 2 → Parameters 2 d) (hq : Measurable q)
    {f : Plane → ℂ} (hf : Integrable f) (p : ℝ) :
    (∫⁻ w, ‖G.finiteSliceMain χ L β r b δ N q f w‖ₑ ^ p ∂finiteSliceMainMeasure N) =
      ∑ j ∈ Finset.range N, ∫⁻ z : Aux 2,
        ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ j) L β r f (q z)‖ₑ ^ p := by
  have hm := (G.e3_measurable_finiteSliceMain hG χ hχ hc L β hβ r b δ N q hq hf).enorm.pow_const p
  rw [finiteSliceMainMeasure, lintegral_prod _ hm.aemeasurable, lintegral_count, tsum_fintype]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫⁻ z : Aux 2,
    ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff χ b δ j) L β r f (q z)‖ₑ ^ p) N

theorem Family.e3_measurable_fullFiniteSliceMain {d : ℕ}
    (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    (r b δ : ℝ) (N : ℕ) {f : Plane → ℂ} (hf : Integrable f) :
    Measurable (G.fullFiniteSliceMain χ L β r b δ N f) := by
  apply measurable_from_prod_countable_right
  intro j
  exact (G.e3_stronglyMeasurable_cutoffPartialExtension hG _
    (hχ.mul ((contDiff_scaleTimeCutoff b δ j.val).continuous.comp continuous_fst))
    (hasCompactSupport_scaleTimeLocalizedCutoff hc b δ j.val)
    L hβ hf r).measurable

end PlanarNikodym
