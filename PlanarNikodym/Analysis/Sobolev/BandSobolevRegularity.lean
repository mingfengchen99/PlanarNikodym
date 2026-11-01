import PlanarNikodym.Analysis.Fourier.FrequencyRegularity
import PlanarNikodym.Analysis.Sobolev.ScaledSobolev

/-! Actual regularity of the compactly cut off curve averages.  Global `C¹`
regularity of the defining function is a sufficient geometric hypothesis;
no regularity of a frequency-localized average is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution NNReal

namespace PlanarNikodym

/-- Integration over a uniformly compact time support preserves the order of
continuous differentiability.  The proof uses parameter-dependent compactly
supported convolution with the constant function one. -/
theorem contDiff_integral_of_compact_time_support
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞} {H : P × ℝ → ℂ} (hH : ContDiff ℝ n H)
    {K : Set ℝ} (hK : IsCompact K) (hs : ∀ p t, t ∉ K → H (p, t) = 0) :
    ContDiff ℝ n (fun p => ∫ t : ℝ, H (p, t)) := by
  have hc : ContDiffOn ℝ n
      (fun p : P => ((fun _ : ℝ => (1 : ℂ)) ⋆[ContinuousLinearMap.mul ℝ ℂ]
        (fun t => H (p, t))) 0) univ := by
    apply contDiffOn_convolution_right_with_param_comp (ContinuousLinearMap.mul ℝ ℂ)
      (v := fun _ : P => (0 : ℝ)) (f := fun _ : ℝ => (1 : ℂ))
      (g := fun p t => H (p, t)) contDiffOn_const isOpen_univ hK
    · exact fun p t _ ht => hs p t ht
    · exact locallyIntegrable_const (1 : ℂ)
    · exact hH.contDiffOn
  have heq : (fun p : P => ((fun _ : ℝ => (1 : ℂ)) ⋆[ContinuousLinearMap.mul ℝ ℂ]
      (fun t => H (p, t))) 0) = (fun p => ∫ t : ℝ, H (p, t)) := by
    funext p
    simp only [convolution_def, ContinuousLinearMap.mul_apply', one_mul, zero_sub]
    exact integral_neg_eq_self (fun t : ℝ => H (p, t)) (volume : Measure ℝ)
  rw [heq] at hc
  exact contDiffOn_univ.mp hc

/-- Actual cutoff averages are jointly `C¹` when the cutoff and the defining
function are globally `C¹`, the cutoff has compact support, and the input is
`C¹`.  The geometric parameter domain may be arbitrary. -/
theorem Family.cutoffAverage_contDiff_one_of_global {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hγ : ContDiff ℝ 1 (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {f : Plane → ℂ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (G.cutoffAverage χ f) := by
  let H : Parameters 2 d × ℝ → ℂ := fun q =>
    (χ (q.2, q.1) : ℂ) * f (q.2, G.γ q.2 q.1)
  have hswap : ContDiff ℝ 1 (fun q : Parameters 2 d × ℝ => (q.2, q.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hH : ContDiff ℝ 1 H :=
    (Complex.ofRealCLM.contDiff.comp (hχ.comp hswap)).mul
      (hf.comp (contDiff_snd.prodMk (hγ.comp hswap)))
  have hK : IsCompact (Prod.fst '' tsupport χ) := hc.isCompact.image continuous_fst
  have hs : ∀ p t, t ∉ Prod.fst '' tsupport χ → H (p, t) = 0 := by
    intro p t ht
    have htp : (t, p) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
    simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]
  exact contDiff_integral_of_compact_time_support hH hK hs

/-- The frequency-localized actual averages have joint `C¹` regularity for
every `L¹` input, derived from the actual Schwartz Fourier kernel. -/
theorem Family.bandAverage_contDiff_one_of_global {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hγ : ContDiff ℝ 1 (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f) :
    ContDiff ℝ 1 (G.cutoffAverage χ (L.band k f)) :=
  G.cutoffAverage_contDiff_one_of_global χ hχ hc hγ (L.band_contDiff_one k hf)

/-- The one-parameter band Sobolev input is now proved from concrete
geometric regularity and compact support.  No band-average regularity or
Sobolev estimate is supplied as an additional input. -/
theorem Family.bandSobolevInput_aux_one_of_global (G : Family 2 1)
    (χ : Cutoff 1) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hγ : ContDiff ℝ 1 (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2))
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) :
    BandSobolevInput G χ L p 1 δ := by
  apply G.bandSobolevInput_aux_one_of_contDiff_bands χ L p hp δ hδ
  intro k f hi _
  exact G.bandAverage_contDiff_one_of_global χ hχ hc hγ L k hi

/-- The actual integrand is jointly `C¹` if the defining function is `C¹`
near each point of the cutoff support.  Outside that support the integrand
agrees with zero on a whole neighborhood. -/
theorem Family.contDiff_one_cutoffIntegrand {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ 1 χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 1 (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (fun x : ℝ × Parameters 2 d =>
      (χ x : ℂ) * f (G.graphMap x.2 x.1)) := by
  have hχC : ContDiff ℝ 1 (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχC.contDiffAt.mul
      (hf.contDiffAt.comp x (contDiffAt_fst.prodMk (hγ x hx)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]

/-- Actual averages are jointly `C¹` under regularity only near the cutoff
support.  No regularity outside the support is required. -/
theorem Family.cutoffAverage_contDiff_one {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 1 (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (G.cutoffAverage χ f) := by
  let H : Parameters 2 d × ℝ → ℂ := fun q =>
    (χ (q.2, q.1) : ℂ) * f (G.graphMap q.1 q.2)
  have hH : ContDiff ℝ 1 H := (G.contDiff_one_cutoffIntegrand χ hχ hγ hf).comp
    (contDiff_snd.prodMk contDiff_fst)
  have hK : IsCompact (Prod.fst '' tsupport χ) := hc.isCompact.image continuous_fst
  have hs : ∀ p t, t ∉ Prod.fst '' tsupport χ → H (p, t) = 0 := by
    intro p t ht
    have htp : (t, p) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
    simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]
  exact contDiff_integral_of_compact_time_support hH hK hs

theorem Family.bandAverage_contDiff_one {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 1 (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f) :
    ContDiff ℝ 1 (G.cutoffAverage χ (L.band k f)) :=
  G.cutoffAverage_contDiff_one χ hχ hc hγ (L.band_contDiff_one k hf)

/-- The one-auxiliary-variable Sobolev input follows from compact cutoff
support and `C¹` regularity near that support. -/
theorem Family.bandSobolevInput_aux_one (G : Family 2 1)
    (χ : Cutoff 1) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 1 (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) :
    BandSobolevInput G χ L p 1 δ := by
  apply G.bandSobolevInput_aux_one_of_contDiff_bands χ L p hp δ hδ
  intro k f hi _
  exact G.bandAverage_contDiff_one χ hχ hc hγ L k hi

/-- For an analytic family, support containment supplies the local geometric
regularity required by the one-parameter band Sobolev theorem. -/
theorem Family.bandSobolevInput_aux_one_of_analytic (G : Family 2 1)
    (hG : G.IsAnalytic) (χ : Cutoff 1) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ G.I.carrier ×ˢ G.W)
    (L : FrequencyCutoff) (p : ℝ≥0) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 ≤ δ) :
    BandSobolevInput G χ L p 1 δ := by
  apply G.bandSobolevInput_aux_one χ hχ hc (fun x hx => (hG x (hs hx)).contDiffAt)
    L p hp δ hδ

end PlanarNikodym
