import PlanarNikodym.Analysis.Jets.CompactTimeJets
import PlanarNikodym.Analysis.Jets.AverageFirstDerivative

/-! Exact higher-jet formulas for the actual curve average, including the
auxiliary jets used by `JetSmoothingInput`. No smoothing bound is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

theorem Family.iteratedFDeriv_cutoffAverage_eq_integral {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (q : Parameters 2 d) :
    iteratedFDeriv ℝ j (G.cutoffAverage χ f) q =
      ∫ t : ℝ, iteratedFDeriv ℝ j (fun r => (χ (t, r) : ℂ) * f (G.graphMap r t)) q := by
  let H : Parameters 2 d × ℝ → ℂ := fun x =>
    (χ (x.2, x.1) : ℂ) * f (G.graphMap x.1 x.2)
  have hH : ContDiff ℝ ∞ H := (G.contDiff_cutoffIntegrand χ hχ hγ hf).comp
    (contDiff_snd.prodMk contDiff_fst)
  apply iteratedFDeriv_integral_of_compact_time_support j hH
    (hc.isCompact.image continuous_fst) _ q
  intro p t ht
  have htp : (t, p) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
  simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]

theorem Family.auxiliary_cutoffJet_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : Base 2) (u : Aux d) :
    Integrable (fun t : ℝ => iteratedFDeriv ℝ j
      (fun v => (χ (t, (z, v)) : ℂ) * f (G.graphMap (z, v) t)) u) := by
  let H : Aux d × ℝ → ℂ := fun x =>
    (χ (x.2, (z, x.1)) : ℂ) * f (G.graphMap (z, x.1) x.2)
  have hH : ContDiff ℝ ∞ H := (G.contDiff_cutoffIntegrand χ hχ hγ hf).comp
    (contDiff_snd.prodMk ((contDiff_const (c := z)).prodMk contDiff_fst))
  apply integrable_parameter_iteratedFDeriv_of_compact_time_support j hH
    (hc.isCompact.image continuous_fst) _ u
  intro v t ht
  have htp : (t, (z, v)) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
  simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]

/-- This is precisely the auxiliary multilinear jet appearing in the
existing scaled jet norm, with all derivatives inside the time integral. -/
theorem Family.auxiliary_cutoffJet_eq_integral {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : Base 2) (u : Aux d) :
    iteratedFDeriv ℝ j (fun v => G.cutoffAverage χ f (z, v)) u =
      ∫ t : ℝ, iteratedFDeriv ℝ j
        (fun v => (χ (t, (z, v)) : ℂ) * f (G.graphMap (z, v) t)) u := by
  let H : Aux d × ℝ → ℂ := fun x =>
    (χ (x.2, (z, x.1)) : ℂ) * f (G.graphMap (z, x.1) x.2)
  have hH : ContDiff ℝ ∞ H := (G.contDiff_cutoffIntegrand χ hχ hγ hf).comp
    (contDiff_snd.prodMk ((contDiff_const (c := z)).prodMk contDiff_fst))
  apply iteratedFDeriv_integral_of_compact_time_support j hH
    (hc.isCompact.image continuous_fst) _ u
  intro v t ht
  have htp : (t, (z, v)) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
  simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]

theorem Family.auxiliary_cutoffJet_apply_eq_integral {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ)
    (z : Base 2) (u : Aux d) (v : Fin j → Aux d) :
    iteratedFDeriv ℝ j (fun u => G.cutoffAverage χ f (z, u)) u v =
      ∫ t : ℝ, iteratedFDeriv ℝ j
        (fun u => (χ (t, (z, u)) : ℂ) * f (G.graphMap (z, u) t)) u v := by
  rw [G.auxiliary_cutoffJet_eq_integral χ hχ hc hγ hf j z u]
  exact ContinuousMultilinearMap.integral_apply
    (G.auxiliary_cutoffJet_integrable χ hχ hc hγ hf j z u) v

theorem Family.auxiliary_bandJet_eq_integral {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f)
    (j : ℕ) (z : Base 2) (u : Aux d) :
    iteratedFDeriv ℝ j (fun v => G.cutoffAverage χ (L.band k f) (z, v)) u =
      ∫ t : ℝ, iteratedFDeriv ℝ j
        (fun v => (χ (t, (z, v)) : ℂ) * L.band k f (G.graphMap (z, v) t)) u :=
  G.auxiliary_cutoffJet_eq_integral χ hχ hc hγ (L.band_contDiff_infty k hf) j z u

end PlanarNikodym
