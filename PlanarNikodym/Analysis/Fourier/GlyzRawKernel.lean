import PlanarNikodym.Analysis.Fourier.GlyzRawParabolicRescaling
import PlanarNikodym.Analysis.Fourier.GlyzDyadicKernelIteration
import PlanarNikodym.Analysis.Fourier.OscillatorySymbolJets
import PlanarNikodym.Analysis.Fourier.GlyzSmoothMovingAtlas

/-! The original extension is the actual smooth compact kernel used by
the dyadic iteration. Frozen-time output cutoffs preserve the original
input integral exactly. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators ENNReal
namespace PlanarNikodym

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def glyzRawKernel (Φ : P × ℝ → ℝ) (a : P × Plane → ℂ) (r : ℝ) (z : P × Plane) : ℂ :=
  phaseOscillation (fun t => Φ (z.1, t)) (r * z.2.2) z.2.1 * a z

theorem contDiff_glyzRawKernel {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (r : ℝ) :
    ContDiff ℝ ∞ (glyzRawKernel Φ a r) := by
  exact ((contDiff_unitImaginaryExponential.comp
    ((contDiff_const.mul contDiff_snd.snd).mul
      (hΦ.comp (contDiff_fst.prodMk contDiff_snd.fst))))).mul ha

omit [NormedSpace ℝ P] in
theorem hasCompactSupport_glyzRawKernel (Φ : P × ℝ → ℝ)
    {a : P × Plane → ℂ} (ha : HasCompactSupport a) (r : ℝ) :
    HasCompactSupport (glyzRawKernel Φ a r) := ha.mul_left

theorem glyzRawExtension_eq_compactKernel {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) (p : P) :
    glyzRawExtension Φ a g r p = ∫ y, g y * glyzRawKernel Φ a r (p, y) := by
  let F : Plane → ℂ := fun y => g y * glyzRawKernel Φ a r (p, y)
  have hi : Integrable F := integrable_compactKernel_smul volume hg
    (contDiff_glyzRawKernel hΦ ha r) (hasCompactSupport_glyzRawKernel Φ hc r) p
  have he := integral_prod_symm F hi
  change glyzRawExtension Φ a g r p = ∫ y, F y ∂volume.prod volume
  rw [he]
  unfold glyzRawExtension
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [F, glyzRawKernel]
  ring

theorem contDiff_glyzRawExtension {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) :
    ContDiff ℝ ∞ (glyzRawExtension Φ a g r) := by
  have he : glyzRawExtension Φ a g r = fun p => ∫ y, g y * glyzRawKernel Φ a r (p, y) :=
    funext (glyzRawExtension_eq_compactKernel hΦ ha hc hg r)
  rw [he]
  exact contDiff_integral_compactKernel_smul volume hg
    (contDiff_glyzRawKernel hΦ ha r) (hasCompactSupport_glyzRawKernel Φ hc r)

theorem hasCompactSupport_glyzRawExtension {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) :
    HasCompactSupport (glyzRawExtension Φ a g r) := by
  have he : glyzRawExtension Φ a g r = fun p => ∫ y, g y * glyzRawKernel Φ a r (p, y) :=
    funext (glyzRawExtension_eq_compactKernel hΦ ha hc hg r)
  rw [he]
  exact hasCompactSupport_integral_compactKernel_smul volume g
    (hasCompactSupport_glyzRawKernel Φ hc r)

theorem memLp_glyzRawExtension [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsFiniteMeasureOnCompacts μ]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {a : P × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {g : Plane → ℂ} (hg : Integrable g) (r : ℝ) (p : ℝ≥0∞) :
    MemLp (glyzRawExtension Φ a g r) p μ :=
  (contDiff_glyzRawExtension hΦ ha hc hg r).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_glyzRawExtension hΦ ha hc hg r)

/- The parent-time cutoff can be moved outside the integral without
modifying the amplitude inside it. -/
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem glyzRawExtension_frozen_cutoff (Φ : P × ℝ → ℝ) (a : P × Plane → ℂ)
    (g : Plane → ℂ) (r c δ : ℝ) {K : Set (ℝ × P)}
    (ha : ∀ p t η, a (p, t, η) ≠ 0 → (t, p) ∈ K)
    (hg : Function.support g ⊆ {y | y.1 ∈ Icc c (c + δ)})
    (χ : ℝ × P → ℝ)
    (hχ : ∀ x ∈ K, |c - x.1| ≤ δ → χ (c, x.2) = 1) (p : P) :
    (χ (c, p) : ℂ) * glyzRawExtension Φ a g r p = glyzRawExtension Φ a g r p := by
  unfold glyzRawExtension
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hga : g (t, η) = 0
  · simp only [hga, mul_zero]
  by_cases haa : a (p, t, η) = 0
  · simp only [haa, mul_zero, zero_mul]
  have ht := hg hga
  have he := hχ (t, p) (ha p t η haa) (abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1, ht.2]⟩)
  rw [he, Complex.ofReal_one, one_mul]

/- Finite chart localization with factors at the frozen parent time.
No time-dependent partition is inserted into the original amplitude. -/
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem glyzRawExtension_frozen_partition {ι : Type*} [Fintype ι]
    (Φ : P × ℝ → ℝ) (a : P × Plane → ℂ) (g : Plane → ℂ) (r c δ : ℝ)
    {K : Set (ℝ × P)} (ha : ∀ p t η, a (p, t, η) ≠ 0 → (t, p) ∈ K)
    (hg : Function.support g ⊆ {y | y.1 ∈ Icc c (c + δ)})
    (χ : ℝ × P → ℝ) (ψ : ι → ℝ × P → ℝ)
    (hχ : ∀ x ∈ K, |c - x.1| ≤ δ → χ (c, x.2) = 1)
    (hψ : ∀ x, ∑ i, ψ i x = χ x) (p : P) :
    (∑ i, (ψ i (c, p) : ℂ) * glyzRawExtension Φ a g r p) =
      glyzRawExtension Φ a g r p := by
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hψ]
  exact glyzRawExtension_frozen_cutoff Φ a g r c δ ha hg χ hχ p

end PlanarNikodym
