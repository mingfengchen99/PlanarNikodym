import PlanarNikodym.Analysis.Fourier.CompactKernelFourier
import PlanarNikodym.Analysis.Fourier.SpectralNeighborhoodApproximation

/-! Fourier concentration of an actual superposition of translated
integrable coefficient functions. Absolute Fubini and translation
invariance transfer the coefficient tails to a cone-neighborhood tail. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform
namespace PlanarNikodym

variable {E Y : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem integral_shift_outside_cthickening_le {K : Set E}
    {a : E} (ha : a ∈ K) (R : ℝ) {B : E → ℂ} (hB : Integrable B) :
    (∫ ξ in (cthickening R K)ᶜ, ‖B (ξ - a)‖) ≤
      ∫ ξ in {ξ : E | R ≤ ‖ξ‖}, ‖B ξ‖ := by
  let T := {ξ : E | R ≤ ‖ξ‖}
  have hT : MeasurableSet T := (isClosed_le continuous_const continuous_norm).measurableSet
  have ht := (hB.norm.indicator hT).comp_sub_right a
  calc
    _ = ∫ ξ, (cthickening R K)ᶜ.indicator (fun ξ => ‖B (ξ - a)‖) ξ :=
      (integral_indicator isClosed_cthickening.measurableSet.compl).symm
    _ ≤ ∫ ξ, T.indicator (fun ξ => ‖B ξ‖) (ξ - a) := by
      apply integral_mono ((hB.comp_sub_right a).norm.indicator
        isClosed_cthickening.measurableSet.compl) ht
      intro ξ
      change (cthickening R K)ᶜ.indicator (fun ξ => ‖B (ξ - a)‖) ξ ≤
        T.indicator (fun ξ => ‖B ξ‖) (ξ - a)
      by_cases hξ : ξ ∈ cthickening R K
      · simp only [mem_compl_iff, hξ, not_true_eq_false, not_false_eq_true,
          indicator_of_notMem]
        exact indicator_nonneg (fun _ _ => norm_nonneg _) _
      · have hh : ξ - a ∈ T := by
          by_contra hn
          have hn' : ‖ξ - a‖ ≤ R := le_of_lt
            (lt_of_not_ge (show ¬R ≤ ‖ξ - a‖ from hn))
          exact hξ (mem_cthickening_of_dist_le ξ a R K ha (by
            simpa only [dist_eq_norm] using hn'))
        rw [indicator_of_mem (show ξ ∈ (cthickening R K)ᶜ from hξ),
          indicator_of_mem hh]
    _ = ∫ ξ, T.indicator (fun ξ => ‖B ξ‖) ξ :=
      integral_sub_right_eq_self _ a
    _ = _ := integral_indicator hT

theorem integrable_shifted_fourier_superposition (μ : Measure Y) [SFinite μ]
    {g : Y → ℂ} (hg : Integrable g μ) {B : E × Y → ℂ} (hB : Continuous B)
    {v : Y → E} (hv : Continuous v)
    (hi : ∀ y, Integrable (fun ξ => B (ξ, y)))
    {D : ℝ} (hD : ∀ y, (∫ ξ, ‖B (ξ, y)‖) ≤ D) :
    Integrable (fun q : Y × E => g q.1 * B (q.2 - v q.1, q.1)) (μ.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun q : Y × E => g q.1 * B (q.2 - v q.1, q.1)) (μ.prod volume) :=
    hg.aestronglyMeasurable.comp_fst.mul
      ((hB.comp ((continuous_snd.sub (hv.comp continuous_fst)).prodMk
        continuous_fst)).aestronglyMeasurable)
  apply (integrable_prod_iff hm).mpr
  refine ⟨ae_of_all _ fun y => ((hi y).comp_sub_right (v y)).const_mul (g y), ?_⟩
  apply (hg.norm.mul_const D).mono' hm.norm.integral_prod_right'
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simp only [norm_mul]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun ξ : E => ‖B (ξ, y)‖) (v y)]
  exact mul_le_mul_of_nonneg_left (hD y) (norm_nonneg _)

theorem integral_fourier_superposition_tail_le (μ : Measure Y) [SFinite μ]
    {g : Y → ℂ} (hg : Integrable g μ) {B : E × Y → ℂ} (hB : Continuous B)
    {v : Y → E} (hv : Continuous v)
    (hi : ∀ y, Integrable (fun ξ => B (ξ, y)))
    {D : ℝ} (hD : ∀ y, (∫ ξ, ‖B (ξ, y)‖) ≤ D)
    {K : Set E} (hvK : ∀ y, g y ≠ 0 → v y ∈ K)
    {R C : ℝ} (ht : ∀ y, (∫ ξ in {ξ : E | R ≤ ‖ξ‖}, ‖B (ξ, y)‖) ≤ C) :
    (∫ ξ in (cthickening R K)ᶜ, ‖∫ y, g y * B (ξ - v y, y) ∂μ‖) ≤
      C * ∫ y, ‖g y‖ ∂μ := by
  let J := fun q : Y × E => g q.1 * B (q.2 - v q.1, q.1)
  have hJ : Integrable J (μ.prod volume) :=
    integrable_shifted_fourier_superposition μ hg hB hv hi hD
  have hJt : Integrable J (μ.prod (volume.restrict (cthickening R K)ᶜ)) := by
    rw [← (Measure.restrict_univ (μ := μ)), Measure.prod_restrict]
    exact hJ.integrableOn
  calc
    _ ≤ ∫ ξ in (cthickening R K)ᶜ, ∫ y, ‖J (y, ξ)‖ ∂μ :=
      integral_mono hJt.integral_prod_right.norm hJt.integral_norm_prod_right
        (fun ξ => norm_integral_le_integral_norm _)
    _ = ∫ y, (∫ ξ in (cthickening R K)ᶜ, ‖J (y, ξ)‖) ∂μ :=
      (integral_integral_swap hJt.norm).symm
    _ ≤ ∫ y, ‖g y‖ * C ∂μ := by
      apply integral_mono hJt.integral_norm_prod_left (hg.norm.mul_const C)
      intro y
      by_cases hy : g y = 0
      · simp [J, hy]
      · simp only [J, norm_mul]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left
          ((integral_shift_outside_cthickening_le (hvK y hy) R (hi y)).trans (ht y))
          (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_comm]

end PlanarNikodym
