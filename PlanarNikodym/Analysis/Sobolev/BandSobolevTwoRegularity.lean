import PlanarNikodym.Analysis.Fourier.SchwartzConvolutionSmooth
import PlanarNikodym.Analysis.Sobolev.BandSobolevRegularity
import PlanarNikodym.Analysis.Sobolev.SobolevAuxTwo

/-! Actual regularity closes the two-auxiliary-variable Sobolev input.
Regularity is required only at the cutoff support; the integrand vanishes
on a neighborhood of every point outside that support. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal

namespace PlanarNikodym

/-- The actual cutoff integrand has the same differentiability order as the
cutoff, input and defining function near the cutoff support. -/
theorem Family.contDiff_cutoffIntegrand {d : ℕ} (G : Family 2 d) {n : ℕ∞}
    (χ : Cutoff d) (hχ : ContDiff ℝ n χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ n (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x : ℝ × Parameters 2 d =>
      (χ x : ℂ) * f (G.graphMap x.2 x.1)) := by
  have hχC : ContDiff ℝ n (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχC.contDiffAt.mul
      (hf.contDiffAt.comp x (contDiffAt_fst.prodMk (hγ x hx)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]

/-- A compact time support permits differentiating the actual curve
integral to any finite order, and also to order `C∞`. -/
theorem Family.cutoffAverage_contDiff {d : ℕ} (G : Family 2 d) {n : ℕ∞}
    (χ : Cutoff d) (hχ : ContDiff ℝ n χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ n (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (G.cutoffAverage χ f) := by
  let H : Parameters 2 d × ℝ → ℂ := fun q =>
    (χ (q.2, q.1) : ℂ) * f (G.graphMap q.1 q.2)
  have hH : ContDiff ℝ n H := (G.contDiff_cutoffIntegrand χ hχ hγ hf).comp
    (contDiff_snd.prodMk contDiff_fst)
  have hK : IsCompact (Prod.fst '' tsupport χ) := hc.isCompact.image continuous_fst
  have hs : ∀ p t, t ∉ Prod.fst '' tsupport χ → H (p, t) = 0 := by
    intro p t ht
    have htp : (t, p) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
    simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]
  exact contDiff_integral_of_compact_time_support hH hK hs

/-- Regularity of the actual frequency-localized average for arbitrary
`L¹` input, derived from its Schwartz convolution kernel. -/
theorem Family.bandAverage_contDiff {d : ℕ} (G : Family 2 d) {n : ℕ∞}
    (χ : Cutoff d) (hχ : ContDiff ℝ n χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ n (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f) :
    ContDiff ℝ n (G.cutoffAverage χ (L.band k f)) := by
  apply G.cutoffAverage_contDiff χ hχ hc hγ
  exact (L.band_contDiff_infty k hf).of_le (by simp)

/-- The two-dimensional Sobolev input is proved from actual local `C²`
geometry and compact cutoff support. No regularity or estimate for the band
average is assumed as a separate input. -/
theorem Family.bandSobolevInput_aux_two (G : Family 2 2)
    (χ : Cutoff 2) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 2 (fun x : ℝ × Parameters 2 2 => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) :
    BandSobolevInput G χ L p 2 δ := by
  apply G.bandSobolevInput_aux_two_of_contDiff_bands χ L p hp δ hδ
  intro k f hi _
  exact G.bandAverage_contDiff χ hχ hc hγ L k hi

end PlanarNikodym
