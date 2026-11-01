import PlanarNikodym.Analysis.Sobolev.BandSobolevTwoRegularity
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! An actual derivative formula for integration over a fixed compact time
support. The compact majorant is constructed from joint smoothness. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff

namespace PlanarNikodym

theorem contDiff_parameter_fderiv
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun q : P × ℝ => fderiv ℝ (fun p => H (p, q.2)) q.1) := by
  have hdup : ContDiff ℝ ∞
      (Function.uncurry (fun q : P × ℝ => fun p : P => H (p, q.2))) :=
    hH.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact hdup.fderiv contDiff_fst (by simp)

theorem integrable_parameter_fderiv_of_compact_time_support
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H)
    {K : Set ℝ} (hK : IsCompact K) (hs : ∀ p t, t ∉ K → H (p, t) = 0) (p : P) :
    Integrable (fun t : ℝ => fderiv ℝ (fun p => H (p, t)) p) := by
  have hd := (contDiff_parameter_fderiv hH).continuous.comp
    ((continuous_const (y := p)).prodMk continuous_id)
  apply hd.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro hK
  intro t ht
  change fderiv ℝ (fun p => H (p, t)) p = 0
  have heq : (fun p => H (p, t)) = fun _ => (0 : E) := funext (fun p => hs p t ht)
  simp only [heq, fderiv_const_apply]

/-- The derivative is the Bochner integral of the actual parameter
derivatives. No derivative bound is assumed as an additional input. -/
theorem hasFDerivAt_integral_of_compact_time_support
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H)
    {K : Set ℝ} (hK : IsCompact K) (hs : ∀ p t, t ∉ K → H (p, t) = 0) (p₀ : P) :
    HasFDerivAt (fun p => ∫ t : ℝ, H (p, t))
      (∫ t : ℝ, fderiv ℝ (fun p => H (p, t)) p₀) p₀ := by
  let D : P × ℝ → P →L[ℝ] E := fun q => fderiv ℝ (fun p => H (p, q.2)) q.1
  have hD : Continuous D := (contDiff_parameter_fderiv hH).continuous
  have hD0 (p : P) (t : ℝ) (ht : t ∉ K) : D (p, t) = 0 := by
    have heq : (fun p => H (p, t)) = fun _ => (0 : E) := funext (fun p => hs p t ht)
    simp only [D, heq, fderiv_const_apply]
  have hFint (p : P) : Integrable (fun t : ℝ => H (p, t)) := by
    apply (hH.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    exact HasCompactSupport.intro hK (hs p)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hK).exists_bound_of_continuousOn
    hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun p t => D (p, t)) (s := closedBall p₀ 1)
    (bound := K.indicator (fun _ => C)) (closedBall_mem_nhds p₀ zero_lt_one)
    (Eventually.of_forall (fun p => (hFint p).aestronglyMeasurable)) (hFint p₀)
    (integrable_parameter_fderiv_of_compact_time_support hH hK hs p₀).aestronglyMeasurable
  · exact ae_of_all _ (fun t p hp => by
      by_cases ht : t ∈ K
      · simpa only [indicator_of_mem ht] using hC (p, t) ⟨hp, ht⟩
      · simp only [hD0 p t ht, norm_zero, indicator_of_notMem ht, le_refl])
  · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.isClosed.measurableSet
  · exact ae_of_all _ (fun t p _ =>
      ((hH.comp (contDiff_id.prodMk (contDiff_const (c := t)))).differentiable
        (by simp) p).hasFDerivAt)

end PlanarNikodym
