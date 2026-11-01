import PlanarNikodym.Analysis.Localization.ScaleTimePartition
import PlanarNikodym.Analysis.Fourier.BandOscillatoryRepresentation

/-! The scale-dependent time partition applied to actual curve cutoffs
and oscillatory amplitudes. Integral decompositions include the required
integrability proofs. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PlanarNikodym

def scaleTimeLocalizedCutoff {P : Type} (χ : ℝ × P → ℝ) (a δ : ℝ) (i : ℕ)
    (x : ℝ × P) : ℝ := χ x * scaleTimeCutoff a δ i x.1

theorem contDiff_scaleTimeLocalizedCutoff
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {χ : ℝ × P → ℝ} (hχ : ContDiff ℝ ∞ χ) (a δ : ℝ) (i : ℕ) :
    ContDiff ℝ ∞ (scaleTimeLocalizedCutoff χ a δ i) :=
  hχ.mul ((contDiff_scaleTimeCutoff a δ i).comp contDiff_fst)

theorem hasCompactSupport_scaleTimeLocalizedCutoff
    {P : Type} [TopologicalSpace P] {χ : ℝ × P → ℝ} (hc : HasCompactSupport χ)
    (a δ : ℝ) (i : ℕ) : HasCompactSupport (scaleTimeLocalizedCutoff χ a δ i) := hc.mul_right

theorem tsupport_scaleTimeLocalizedCutoff_subset
    {P : Type} [TopologicalSpace P] (χ : ℝ × P → ℝ) (a δ : ℝ) (i : ℕ) :
    tsupport (scaleTimeLocalizedCutoff χ a δ i) ⊆ tsupport χ := tsupport_mul_subset_left

theorem scaleTimeLocalizedCutoff_time_support
    {P : Type} [TopologicalSpace P] (χ : ℝ × P → ℝ) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ)
    {x : ℝ × P} (hx : x ∈ tsupport (scaleTimeLocalizedCutoff χ a δ i)) :
    x.1 ∈ Icc (a + ((i : ℝ) - 1) * δ) (a + ((i : ℝ) + 1) * δ) := by
  have hs : tsupport (scaleTimeLocalizedCutoff χ a δ i) ⊆
      tsupport (fun x : ℝ × P => scaleTimeCutoff a δ i x.1) := tsupport_mul_subset_right
  exact tsupport_scaleTimeCutoff_subset a hδ i
    ((tsupport_comp_subset_preimage _ continuous_fst) (hs hx))

theorem sum_scaleTimeLocalizedCutoff
    {P : Type} (χ : ℝ × P → ℝ) (a b : ℝ) {δ : ℝ} (_hδ : 0 < δ)
    (N : ℕ) (hN : ∀ t ∈ Icc a b, ∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t = 1)
    (hs : ∀ x, χ x ≠ 0 → x.1 ∈ Icc a b) (x : ℝ × P) :
    ∑ i ∈ Finset.range N, scaleTimeLocalizedCutoff χ a δ i x = χ x := by
  by_cases hx : χ x = 0
  · simp only [scaleTimeLocalizedCutoff, hx, zero_mul, Finset.sum_const_zero]
  · simp only [scaleTimeLocalizedCutoff, ← Finset.mul_sum, hN x.1 (hs x hx), mul_one]

/-- An integrable function with bounded time support splits exactly into
the smooth scale pieces, each of which remains integrable. -/
theorem integral_eq_sum_scaleTimeCutoff
    {F : ℝ → ℂ} (hF : Integrable F) (a b : ℝ) {δ : ℝ} (_hδ : 0 < δ)
    (N : ℕ) (hN : ∀ t ∈ Icc a b, ∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t = 1)
    (hs : ∀ t, F t ≠ 0 → t ∈ Icc a b) :
    (∫ t : ℝ, F t) = ∑ i ∈ Finset.range N, ∫ t : ℝ, (scaleTimeCutoff a δ i t : ℂ) * F t := by
  have hi (i : ℕ) : Integrable (fun t : ℝ => (scaleTimeCutoff a δ i t : ℂ) * F t) := by
    apply hF.norm.mono'
    · exact (Complex.continuous_ofReal.comp (contDiff_scaleTimeCutoff a δ i).continuous).aestronglyMeasurable.mul
        hF.aestronglyMeasurable
    · filter_upwards [] with t
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (scaleTimeCutoff_nonneg a δ t i)]
      exact mul_le_of_le_one_left (norm_nonneg _) (scaleTimeCutoff_le_one a δ t i)
  rw [← integral_finsetSum (Finset.range N) (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : F t = 0
  · simp only [ht, mul_zero, Finset.sum_const_zero]
  · rw [← Finset.sum_mul, ← Complex.ofReal_sum, hN t (hs t ht), Complex.ofReal_one, one_mul]

/-- The same exact decomposition for the actual curve oscillatory
amplitude, retaining the original geometry and the localized cutoffs. -/
theorem Family.cutoffOscillatoryAmplitude_eq_sum_scaleTimeLocalized
    {d : ℕ} (G : Family 2 d) (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x => G.γ x.1 x.2) x)
    (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hN : ∀ t ∈ Icc a b, ∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t = 1)
    (hs : ∀ x ∈ tsupport χ, x.1 ∈ Icc a b) (q : Parameters 2 d) (ξ : Plane) :
    G.cutoffOscillatoryAmplitude χ q ξ = ∑ i ∈ Finset.range N,
      G.cutoffOscillatoryAmplitude (scaleTimeLocalizedCutoff χ a δ i) q ξ := by
  let F : ℝ → ℂ := fun t => (χ (t, q) : ℂ) * planeFourierCharacter (G.graphMap q t) ξ
  have hFc : Continuous F :=
    (G.continuous_cutoffOscillatoryIntegrand χ hχ hγ q).comp
      (continuous_id.prodMk continuous_const)
  have hF : Integrable F := hFc.integrable_of_hasCompactSupport
    (((cutoffSlice_hasCompactSupport χ hc q).comp_left (g := Complex.ofRealCLM) rfl).mul_right)
  have hsF : ∀ t, F t ≠ 0 → t ∈ Icc a b := by
    intro t ht
    have hχt : χ (t, q) ≠ 0 := by
      intro hz
      exact ht (by simp only [F, hz, Complex.ofReal_zero, zero_mul])
    exact hs (t, q) (subset_closure hχt)
  have he := integral_eq_sum_scaleTimeCutoff hF a b hδ N hN hsF
  calc
    _ = ∫ t : ℝ, F t := rfl
    _ = ∑ i ∈ Finset.range N, ∫ t : ℝ, (scaleTimeCutoff a δ i t : ℂ) * F t := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [F, scaleTimeLocalizedCutoff, Complex.ofReal_mul]
      ring

end PlanarNikodym
