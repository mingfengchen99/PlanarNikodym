import PlanarNikodym.Analysis.Fourier.PartialExtensionLInfinity
import PlanarNikodym.Analysis.Sobolev.BandSobolevTwoRegularity

/-! Regularity and signed-cutoff linearity for the actual normalized
physical multiplier, used when assembling scalar smoothing. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlanarNikodym

theorem contDiff_scaledFrequencyConvolution {m : Plane → ℝ}
    (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m) {r : ℝ} (hr : r ≠ 0)
    {f : Plane → ℂ} (hf : Integrable f) :
    ContDiff ℝ ∞ (scaledFrequencyConvolution m r f) := by
  let e : Plane ≃L[ℝ] Plane := (LinearEquiv.smulOfNeZero ℝ Plane r hr).toContinuousLinearEquiv
  let K := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (inverseFourierSchwartz m hm hc)
  have h := (contDiff_infty_integral_schwartz_mul hf K).const_smul (r ^ 2)
  have he (x : Plane) : e x = r • x := rfl
  have hK (x : Plane) : K x = inverseFourierIntegral m (r • x) := by
    change inverseFourierSchwartz m hm hc (e x) = _
    rw [he, inverseFourierSchwartz_apply]
  unfold scaledFrequencyConvolution
  simpa only [hK] using h

theorem Family.cutoffAverage_sub_cutoff {d : ℕ} (G : Family 2 d)
    (χ₁ χ₂ : Cutoff d) (hχ₁ : Continuous χ₁) (hχ₂ : Continuous χ₂)
    (hc₁ : HasCompactSupport χ₁) (hc₂ : HasCompactSupport χ₂)
    (hγ₁ : ∀ x ∈ tsupport χ₁, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (hγ₂ : ∀ x ∈ tsupport χ₂, ContinuousAt (fun x => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : Continuous f) :
    G.cutoffAverage (χ₁ - χ₂) f = G.cutoffAverage χ₁ f - G.cutoffAverage χ₂ f := by
  funext q
  simp only [Family.cutoffAverage, Pi.sub_apply, Complex.ofReal_sub, sub_mul]
  exact integral_sub (G.cutoffIntegrand_integrable χ₁ hχ₁ hc₁ hγ₁ hf q)
    (G.cutoffIntegrand_integrable χ₂ hχ₂ hc₂ hγ₂ hf q)

end PlanarNikodym
