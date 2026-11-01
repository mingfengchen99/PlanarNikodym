import PlanarNikodym.Analysis.Jets.AverageHigherDerivatives
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-! An exact finite Faa di Bruno expansion for the actual auxiliary jets.
The inner map contains only cutoff and geometry, while the outer map
contains the input. Uniform oscillatory estimates remain a separate task. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PlanarNikodym

/-- A local version of the finite Faa di Bruno formula, requiring the
inner map to be smooth only at the point in question. -/
theorem iteratedFDeriv_comp_eq_sum_orderedFinpartition
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {j : ℕ} {g : E → F} {f : P → E} {x : P}
    (hg : ContDiff ℝ j g) (hf : ContDiffAt ℝ j f x) :
    iteratedFDeriv ℝ j (g ∘ f) x =
      ∑ c : OrderedFinpartition j, (ftaylorSeries ℝ g (f x)).compAlongOrderedFinpartition
        (ftaylorSeries ℝ f x) c := by
  classical
  obtain ⟨U, hU, hxU, hfU'⟩ := hf.contDiffOn' le_rfl (by simp)
  have hfU : ContDiffOn ℝ j f U := by simpa using hfU'
  have ht := ((hg.ftaylorSeries.hasFTaylorSeriesUpToOn univ).comp
    (hfU.ftaylorSeriesWithin hU.uniqueDiffOn) (mapsTo_univ f U)).eq_iteratedFDerivWithin_of_uniqueDiffOn
      le_rfl hU.uniqueDiffOn hxU
  have heq : ftaylorSeriesWithin ℝ f U x = ftaylorSeries ℝ f x := by
    funext n
    exact iteratedFDerivWithin_of_isOpen n hU hxU
  simpa only [heq, FormalMultilinearSeries.taylorComp,
    iteratedFDerivWithin_of_isOpen j hU hxU] using ht.symm

def jetInputProduct (f : Plane → ℂ) (x : ℂ × Plane) : ℂ := x.1 * f x.2

def Family.cutoffGraphMap {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (z : Base 2) (t : ℝ) (u : Aux d) : ℂ × Plane :=
  ((χ (t, (z, u)) : ℂ), G.graphMap (z, u) t)

/-- A finite, explicit multilinear amplitude. It uses only jets of the
input product and the geometry/cutoff map, and is zero off the cutoff support. -/
def Family.cutoffJetAmplitude {d : ℕ} (G : Family 2 d) (χ : Cutoff d)
    (f : Plane → ℂ) (j : ℕ) (z : Base 2) (t : ℝ) (u : Aux d) : Aux d [×j]→L[ℝ] ℂ := by
  classical
  exact if (t, (z, u)) ∈ tsupport χ then
    ∑ c : OrderedFinpartition j,
      (ftaylorSeries ℝ (jetInputProduct f) (G.cutoffGraphMap χ z t u)).compAlongOrderedFinpartition
        (ftaylorSeries ℝ (G.cutoffGraphMap χ z t) u) c
    else 0

/-- Every actual auxiliary integrand jet equals the finite chain-rule
amplitude, including points where the geometric extension is irregular
outside the cutoff support. -/
theorem Family.auxiliary_cutoffIntegrandJet_eq_amplitude {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (z : Base 2) (t : ℝ) (u : Aux d) :
    iteratedFDeriv ℝ j (fun v => (χ (t, (z, v)) : ℂ) * f (G.graphMap (z, v) t)) u =
      G.cutoffJetAmplitude χ f j z t u := by
  classical
  by_cases hx : (t, (z, u)) ∈ tsupport χ
  · have houter : ContDiff ℝ ∞ (jetInputProduct f) :=
      contDiff_fst.mul (hf.comp contDiff_snd)
    have hemb : ContDiffAt ℝ ∞ (fun v : Aux d => (t, (z, v))) u :=
      contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)
    have hγu : ContDiffAt ℝ ∞ (fun v => G.γ t (z, v)) u :=
      (hγ (t, (z, u)) hx).comp (f := fun v : Aux d => (t, (z, v))) u hemb
    have hχu : ContDiff ℝ ∞ (fun v : Aux d => (χ (t, (z, v)) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        (hχ.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))
    have hinner : ContDiffAt ℝ ∞ (G.cutoffGraphMap χ z t) u :=
      hχu.contDiffAt.prodMk (contDiffAt_const.prodMk hγu)
    simpa only [Family.cutoffJetAmplitude, if_pos hx, jetInputProduct, Family.cutoffGraphMap,
      Function.comp_def] using iteratedFDeriv_comp_eq_sum_orderedFinpartition
        (contDiff_infty.mp houter j) (contDiffAt_infty.mp hinner j)
  · have he : (fun v : Aux d => (χ (t, (z, v)) : ℂ) * f (G.graphMap (z, v) t)) =ᶠ[𝓝 u]
        fun _ => 0 := by
      have hcont : ContinuousAt (fun v : Aux d => (t, (z, v))) u :=
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
      filter_upwards [hcont.eventually ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)] with v hv
      simp only [image_eq_zero_of_notMem_tsupport hv, Complex.ofReal_zero, zero_mul]
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [Family.cutoffJetAmplitude, if_neg hx]
    cases j with
    | zero => simp
    | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply]

theorem Family.cutoffJetAmplitude_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : Base 2) (u : Aux d) :
    Integrable (fun t : ℝ => G.cutoffJetAmplitude χ f j z t u) := by
  exact (G.auxiliary_cutoffJet_integrable χ hχ hc hγ hf j z u).congr
    (ae_of_all _ (fun t => G.auxiliary_cutoffIntegrandJet_eq_amplitude χ hχ hγ hf j z t u))

theorem Family.auxiliary_cutoffJet_eq_integral_amplitude {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : Base 2) (u : Aux d) :
    iteratedFDeriv ℝ j (fun v => G.cutoffAverage χ f (z, v)) u =
      ∫ t : ℝ, G.cutoffJetAmplitude χ f j z t u := by
  rw [G.auxiliary_cutoffJet_eq_integral χ hχ hc hγ hf j z u]
  exact integral_congr_ae (ae_of_all _
    (fun t => G.auxiliary_cutoffIntegrandJet_eq_amplitude χ hχ hγ hf j z t u))

theorem Family.auxiliary_bandJet_eq_integral_amplitude {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f)
    (j : ℕ) (z : Base 2) (u : Aux d) :
    iteratedFDeriv ℝ j (fun v => G.cutoffAverage χ (L.band k f) (z, v)) u =
      ∫ t : ℝ, G.cutoffJetAmplitude χ (L.band k f) j z t u :=
  G.auxiliary_cutoffJet_eq_integral_amplitude χ hχ hc hγ (L.band_contDiff_infty k hf) j z u

end PlanarNikodym
