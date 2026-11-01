import PlanarNikodym.Analysis.Fourier.PhysicalInputLocalization
import PlanarNikodym.Analysis.Fourier.PartialExtensionLinearity
import PlanarNikodym.Analysis.Jets.ScalarJetFourier

/-! Actual polynomial Lp bounds at all frequencies, used to cover the
bounded low-frequency range in the final scalar smoothing estimate. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal
namespace PlanarNikodym
set_option maxHeartbeats 800000

theorem continuous_scaledFrequencyConvolution {m : Plane → ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) {f : Plane → ℂ}
    (hf : Integrable f) (r : ℝ) : Continuous (scaledFrequencyConvolution m r f) := by
  have hA : Continuous (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
    (Complex.continuous_ofReal.comp hm).mul
      ((continuous_planeFourierIntegral hf).comp (continuous_const.smul continuous_id))
  have hcA : HasCompactSupport (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
    (hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right
  have he : scaledFrequencyConvolution m r f = fun x => r ^ 2 •
      ∫ ξ : Plane, ((m ξ : ℂ) * planeFourierIntegral f (r • ξ)) * planeFourierCharacter x (r • ξ) :=
    funext (scaledFrequencyConvolution_eq_fourierIntegral hm (hm.integrable_of_hasCompactSupport hc) hf r)
  rw [he]
  exact (continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_scalarJet_fourierIntegral hA hcA r x).continuousAt).const_smul _

theorem Family.continuous_partialExtension_of_support {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : Continuous β)
    {f : Plane → ℂ} (hf : Integrable f) (r : ℝ) :
    Continuous (G.cutoffPartialExtension χ L β r f) := by
  have he : G.cutoffPartialExtension χ L β r f = G.cutoffAverage χ
      (scaledFrequencyConvolution (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2) r f) := by
    funext q
    exact G.cutoffPartialExtension_eq_scaledFrequencyConvolution χ hχ.continuous hc
      (fun x hx => (hγ x hx).continuousAt) L β hβ hf r q
  rw [he]
  apply (G.cutoffAverage_contDiff χ (hχ.of_le (by simp)) hc
    (fun x hx => (hγ x hx).of_le (by simp)) (n := 0) _).continuous
  exact contDiff_zero.mpr (continuous_scaledFrequencyConvolution
    ((L.bandSymbol_smooth 0).continuous.mul (hβ.comp continuous_snd))
    (L.bandSymbol_compact 0).mul_right hf r)

theorem scaledFrequencyConvolution_enorm_le_Lp {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) {f : Plane → ℂ}
    (hf : Integrable f) {p q : ℝ≥0∞} [ENNReal.HolderConjugate q p]
    {r : ℝ} (hr : 1 ≤ r) (x : Plane) :
    ‖scaledFrequencyConvolution m r f x‖ₑ ≤ ENNReal.ofReal (r ^ 2) *
      eLpNorm (inverseFourierIntegral m) q volume * eLpNorm f p volume := by
  let K := inverseFourierIntegral m
  have hK : Continuous K := (inverseFourierIntegral_smooth m hm hc).continuous
  have hH : (∫⁻ y : Plane, ‖K (r • (x - y)) * f y‖ₑ) ≤
      eLpNorm (fun y : Plane => K (r • (x - y))) q volume * eLpNorm f p volume := by
    change (∫⁻ y : Plane, ‖((fun y : Plane => K (r • (x - y))) • f) y‖ₑ) ≤ _
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℂ) hf.aestronglyMeasurable
      (hK.comp (continuous_const.smul (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hkn : eLpNorm (fun y : Plane => K (r • (x - y))) q volume ≤ eLpNorm K q volume := by
    rw [show (fun y : Plane => K (r • (x - y))) =
      (fun y : Plane => K (r • y)) ∘ (fun y : Plane => x - y) from rfl,
      eLpNorm_comp_measurePreserving (g := fun y : Plane => K (r • y)) (p := q)
        (hK.comp (continuous_const.smul continuous_id)).aestronglyMeasurable
        (Measure.measurePreserving_sub_left volume x)]
    exact eLpNorm_plane_dilate_le K hK hr q
  unfold scaledFrequencyConvolution
  rw [enorm_smul, Real.enorm_eq_ofReal (sq_nonneg r)]
  exact (mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _).trans
    ((mul_le_mul_right hH _).trans (by
      rw [← mul_assoc]
      exact mul_le_mul_left (mul_le_mul_right hkn _) _))

/-- A universal quadratic frequency bound for the genuine main term.
It is only used on a fixed bounded frequency interval. -/
theorem Family.exists_partialExtension_polynomial_Lp_bound {d : ℕ}
    (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
      eLpNorm (G.cutoffPartialExtension χ L β r f) p volume ≤
        ENNReal.ofReal (C * r ^ 2) * eLpNorm f p volume := by
  let m : Plane → ℝ := fun ξ => L.bandSymbol 0 ξ * β ξ.2
  have hm : ContDiff ℝ ∞ m := (L.bandSymbol_smooth 0).mul (hβ.comp contDiff_snd)
  have hcm : HasCompactSupport m := (L.bandSymbol_compact 0).mul_right
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  letI : ENNReal.HolderConjugate q p := by
    rw [ENNReal.holderConjugate_iff]
    dsimp only [q]
    rw [inv_inv]
    exact tsub_add_cancel_of_le (by simpa using ENNReal.inv_le_inv.mpr hp)
  let K := inverseFourierSchwartz m hm hcm
  have hK := K.memLp (μ := volume) (p := q)
  let V := (eLpNorm (inverseFourierIntegral m) q volume).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have heV : eLpNorm (inverseFourierIntegral m) q volume = ENNReal.ofReal V := by
    rw [ENNReal.ofReal_toReal]
    simpa only [K, inverseFourierSchwartz_coe] using hK.eLpNorm_ne_top
  obtain ⟨A, hA, havg⟩ := G.exists_cutoffAverage_Lp_of_graph_bound χ hχ hc p
  refine ⟨A * V, mul_nonneg hA hV, ?_⟩
  intro r hr f hf
  have hb : ∀ x ∈ tsupport χ, ‖scaledFrequencyConvolution m r f (G.graphMap x.2 x.1)‖ₑ ≤
      ENNReal.ofReal (V * r ^ 2) * eLpNorm f p volume := by
    intro x _
    have h := scaledFrequencyConvolution_enorm_le_Lp hm hcm hf (p := p) (q := q) hr
      (G.graphMap x.2 x.1)
    rw [heV, ← ENNReal.ofReal_mul (sq_nonneg r), mul_comm (r ^ 2) V] at h
    exact h
  have h := havg (scaledFrequencyConvolution m r f) (V * r ^ 2) (by positivity)
    (eLpNorm f p volume) hb
  have he : G.cutoffPartialExtension χ L β r f =
      G.cutoffAverage χ (scaledFrequencyConvolution m r f) := by
    funext z
    exact G.cutoffPartialExtension_eq_scaledFrequencyConvolution χ hχ hc hγ L β hβ.continuous hf r z
  rw [he]
  simpa only [mul_assoc] using h

end PlanarNikodym
