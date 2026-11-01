import PlanarNikodym.Analysis.Maximal.E2StrongNormInterpolation
import PlanarNikodym.Analysis.Maximal.E2BandSublinearity

/-! The proven finite-endpoint interpolation theorem applied to the
actual dyadic convolution followed by the pointwise auxiliary supremum.
No linearization, measurable choice of maximizers, or representative of
an Lᵖ class is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem Family.cutoffMaximal_band_finite_interpolation_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ)
    {p q₀ q₁ C₀ C₁ B : ℝ} (hq₀ : 0 < q₀) (hqp : q₀ < p)
    (hpq : p < q₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hB : 0 < B)
    (hlo : ∀ g : Plane → ℂ, Integrable g → MemLp g (ENNReal.ofReal q₀) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k g)) (ENNReal.ofReal q₀) volume ≤
        ENNReal.ofReal C₀ * eLpNorm g (ENNReal.ofReal q₀) volume)
    (hhi : ∀ g : Plane → ℂ, Integrable g → MemLp g (ENNReal.ofReal q₁) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k g)) (ENNReal.ofReal q₁) volume ≤
        ENNReal.ofReal C₁ * eLpNorm g (ENNReal.ofReal q₁) volume)
    {f : Plane → ℂ} (hf : Integrable f) (hfp : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (G.cutoffMaximal χ (L.band k f)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((p * ((2 : ℝ) ^ q₀ * C₀ ^ q₀ * B ^ (p - q₀) / (p - q₀) +
        (2 : ℝ) ^ q₁ * C₁ ^ q₁ * B ^ (p - q₁) / (q₁ - p))) ^ (1 / p)) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  let T := G.bandMaximalComplex_e2 χ L k
  have hs : ∀ g h : Plane → ℂ, Integrable g → Integrable h → ∀ z,
      ‖T (g + h) z‖ ≤ ‖T g z‖ + ‖T h z‖ := by
    intro g h hg hh z
    exact G.bandMaximalComplex_e2_subadditive χ hχ hc hγ L k hg hh z
  have hm : ∀ g : Plane → ℂ, Integrable g → Measurable (T g) :=
    fun g hg => G.bandMaximalComplex_e2_measurable χ hχ hc hγ L k hg
  have he : ∀ f g : Plane → ℂ, Integrable f → Integrable g →
      f =ᵐ[volume] g → T f =ᵐ[volume] T g := by
    intro f g _ _ hfg
    have hband := L.band_congr_ae_input k hfg
    exact Filter.Eventually.of_forall (fun z => by dsimp [T, Family.bandMaximalComplex_e2]; rw [hband])
  have hb := e2_sublinear_finite_interpolation volume volume T hs hm he hq₀ hqp hpq
    hC₀ hC₁ hB
    (fun g hg hlp => by
      rw [show T g = G.bandMaximalComplex_e2 χ L k g from rfl,
        G.bandMaximalComplex_e2_eLpNorm χ hχ hc L k hg]
      exact hlo g hg hlp)
    (fun g hg hlp => by
      rw [show T g = G.bandMaximalComplex_e2 χ L k g from rfl,
        G.bandMaximalComplex_e2_eLpNorm χ hχ hc L k hg]
      exact hhi g hg hlp) hf hfp
  rwa [show T f = G.bandMaximalComplex_e2 χ L k f from rfl,
    G.bandMaximalComplex_e2_eLpNorm χ hχ hc L k hf] at hb

end PlanarNikodym
