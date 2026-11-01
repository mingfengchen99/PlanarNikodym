import PlanarNikodym.Analysis.Jets.CompactTimeDerivative

/-! Actual first parameter derivatives of curve averages. The formula
retains both the differentiated cutoff and the differentiated input. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PlanarNikodym

/-- The pointwise amplitude produced by the first parameter derivative.
The defining function only needs to be smooth on the cutoff support. -/
theorem Family.fderiv_cutoffIntegrand_apply {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (q v : Parameters 2 d) :
    fderiv ℝ (fun r => (χ (t, r) : ℂ) * f (G.graphMap r t)) q v =
      (fderiv ℝ (fun r => χ (t, r)) q v : ℂ) * f (G.graphMap q t) +
      (χ (t, q) : ℂ) * fderiv ℝ f (G.graphMap q t)
        (0, fderiv ℝ (fun r => G.γ t r) q v) := by
  by_cases hx : (t, q) ∈ tsupport χ
  · have hχd := ((hχ.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable
      (by simp) q).hasFDerivAt
    have hγd := ((hγ (t, q) hx).comp q
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hg := (hasFDerivAt_const t q).prodMk hγd.hasFDerivAt
    have hI := (Complex.ofRealCLM.hasFDerivAt.comp q hχd).mul
      ((hf.differentiable (by simp) (G.graphMap q t)).hasFDerivAt.comp q hg)
    have heq := congrArg (fun D : Parameters 2 d →L[ℝ] ℂ => D v) hI.fderiv
    simpa [Function.comp_def, Pi.mul_def, Family.graphMap, smul_eq_mul, mul_comm, add_comm] using heq
  · have hz : (fun r : Parameters 2 d => χ (t, r)) =ᶠ[𝓝 q] fun _ => 0 := by
      have ht : ContinuousAt (fun r : Parameters 2 d => (t, r)) q :=
        (continuous_const.prodMk continuous_id :
        Continuous (fun r : Parameters 2 d => (t, r))).continuousAt
      filter_upwards [ht.eventually ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)] with r hr
      exact image_eq_zero_of_notMem_tsupport hr
    have hIz : (fun r => (χ (t, r) : ℂ) * f (G.graphMap r t)) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hz] with r hr
      simp only [hr, Complex.ofReal_zero, zero_mul]
    rw [hIz.fderiv_eq, hz.fderiv_eq]
    simp only [fderiv_const_apply, zero_apply, Complex.ofReal_zero,
      zero_mul, image_eq_zero_of_notMem_tsupport hx, add_zero]

theorem Family.cutoffIntegrand_fderiv_integrable {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (q : Parameters 2 d) :
    Integrable (fun t : ℝ => fderiv ℝ
      (fun r => (χ (t, r) : ℂ) * f (G.graphMap r t)) q) := by
  let H : Parameters 2 d × ℝ → ℂ := fun x =>
    (χ (x.2, x.1) : ℂ) * f (G.graphMap x.1 x.2)
  have hH : ContDiff ℝ ∞ H := (G.contDiff_cutoffIntegrand χ hχ hγ hf).comp
    (contDiff_snd.prodMk contDiff_fst)
  apply integrable_parameter_fderiv_of_compact_time_support hH
    (hc.isCompact.image continuous_fst) _ q
  intro p t ht
  have htp : (t, p) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
  simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]

/-- Differentiation under the actual curve integral, as an equality of
continuous linear maps. -/
theorem Family.fderiv_cutoffAverage_eq_integral {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (q : Parameters 2 d) :
    fderiv ℝ (G.cutoffAverage χ f) q =
      ∫ t : ℝ, fderiv ℝ (fun r => (χ (t, r) : ℂ) * f (G.graphMap r t)) q := by
  let H : Parameters 2 d × ℝ → ℂ := fun x =>
    (χ (x.2, x.1) : ℂ) * f (G.graphMap x.1 x.2)
  have hH : ContDiff ℝ ∞ H := (G.contDiff_cutoffIntegrand χ hχ hγ hf).comp
    (contDiff_snd.prodMk contDiff_fst)
  have hs : ∀ p t, t ∉ Prod.fst '' tsupport χ → H (p, t) = 0 := by
    intro p t ht
    have htp : (t, p) ∉ tsupport χ := fun h => ht (mem_image_of_mem Prod.fst h)
    simp only [H, image_eq_zero_of_notMem_tsupport htp, Complex.ofReal_zero, zero_mul]
  exact (hasFDerivAt_integral_of_compact_time_support hH
    (hc.isCompact.image continuous_fst) hs q).fderiv

/-- The explicit first derivative keeps the two amplitudes arising from
the product and chain rules. Higher-jet frequency bounds are a later task. -/
theorem Family.fderiv_cutoffAverage_apply {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (q v : Parameters 2 d) :
    fderiv ℝ (G.cutoffAverage χ f) q v = ∫ t : ℝ,
      (fderiv ℝ (fun r => χ (t, r)) q v : ℂ) * f (G.graphMap q t) +
      (χ (t, q) : ℂ) * fderiv ℝ f (G.graphMap q t)
        (0, fderiv ℝ (fun r => G.γ t r) q v) := by
  rw [G.fderiv_cutoffAverage_eq_integral χ hχ hc hγ hf q,
    ContinuousLinearMap.integral_apply (G.cutoffIntegrand_fderiv_integrable χ hχ hc hγ hf q) v]
  exact integral_congr_ae (ae_of_all _ (fun t => G.fderiv_cutoffIntegrand_apply χ hχ hγ hf t q v))

/-- The same actual derivative formula applies to every dyadic band of an
arbitrary integrable input, using the proved Schwartz-kernel regularity. -/
theorem Family.fderiv_bandAverage_apply {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) (k : ℕ) {f : Plane → ℂ} (hf : Integrable f)
    (q v : Parameters 2 d) :
    fderiv ℝ (G.cutoffAverage χ (L.band k f)) q v = ∫ t : ℝ,
      (fderiv ℝ (fun r => χ (t, r)) q v : ℂ) * L.band k f (G.graphMap q t) +
      (χ (t, q) : ℂ) * fderiv ℝ (L.band k f) (G.graphMap q t)
        (0, fderiv ℝ (fun r => G.γ t r) q v) :=
  G.fderiv_cutoffAverage_apply χ hχ hc hγ (L.band_contDiff_infty k hf) q v

end PlanarNikodym
