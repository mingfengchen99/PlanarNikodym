import PlanarNikodym.Analysis.Fourier.TimeSliceExtension
import PlanarNikodym.Geometry.ParameterLebesgueCoordinates

/-! Measurability and Tonelli for the actual partial-Fourier extension,
with original parameters, rather than a hypothetical model operator. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem Family.stronglyMeasurable_cutoffPartialExtension {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (L : FrequencyCutoff) {β : ℝ → ℝ} (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    StronglyMeasurable (G.cutoffPartialExtension χ L β r f) := by
  let Φ : ℝ × Parameters 2 d → ℝ := fun x => G.γ x.1 x.2
  obtain ⟨Ψ, N, hΨ, _, _, hKN, _, heq⟩ := exists_compact_smooth_extension Φ hc.isCompact
    (isOpen_analyticAt ℝ Φ) hγ (fun x hx => hx.contDiffAt)
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
  funext q
  unfold Family.cutoffPartialExtension
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hz : χ (t, q) = 0
  · simp [H, hz]
  · have he := heq (hKN (subset_closure hz))
    change Ψ (t, q) = G.γ t q at he
    simp only [H, he]
    rfl

theorem Family.lintegral_cutoffPartialExtension_selected_parameters {d m : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x)
    (L : FrequencyCutoff) {β : ℝ → ℝ} (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ)
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2)) (p : ℝ) :
    (∫⁻ q, ‖G.cutoffPartialExtension χ L β r f q‖ₑ ^ p) =
      ∫⁻ u : UnselectedCoordinates σ, ∫⁻ z : Aux m,
        ‖G.cutoffPartialExtension χ L β r f
          (parameterFrame d (v + selectedCoordinateSplit σ (z, u)))‖ₑ ^ p := by
  exact lintegral_original_selected_parameters σ v _
    ((G.stronglyMeasurable_cutoffPartialExtension χ hχ hc hγ L hβ hf r).measurable.enorm.pow_const p)

end PlanarNikodym
