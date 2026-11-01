import PlanarNikodym.Analysis.Jets.CompactTimeJets
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Smooth parameter dependence of integration over a fixed compact set.
The domination constants are constructed on compact parameter balls;
no bound for the parameter derivatives is supplied as a new input. -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff Interval
universe u

namespace PlanarNikodym

theorem hasFDerivAt_setIntegral_of_joint_contDiff
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H)
    {K : Set ℝ} (hK : IsCompact K) (p₀ : P) :
    HasFDerivAt (fun p => ∫ t in K, H (p, t))
      (∫ t in K, fderiv ℝ (fun p => H (p, t)) p₀) p₀ := by
  let D : P × ℝ → P →L[ℝ] E := fun q => fderiv ℝ (fun p => H (p, q.2)) q.1
  have hD : Continuous D := (contDiff_parameter_fderiv hH).continuous
  have hFint (p : P) : IntegrableOn (fun t => H (p, t)) K :=
    (hH.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
  have hDint (p : P) : IntegrableOn (fun t => D (p, t)) K :=
    (hD.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod hK).exists_bound_of_continuousOn
    hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun p t => D (p, t)) (s := closedBall p₀ 1) (bound := fun _ => C)
    (closedBall_mem_nhds p₀ zero_lt_one)
    (Eventually.of_forall (fun p => (hFint p).aestronglyMeasurable)) (hFint p₀)
    (hDint p₀).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    intro p hp
    exact hC (p, t) ⟨hp, ht⟩
  · exact integrableOn_const hK.measure_ne_top
  · exact ae_of_all _ (fun t p _ =>
      ((hH.comp (contDiff_id.prodMk (contDiff_const (c := t)))).differentiable
        (by simp) p).hasFDerivAt)

/-- All finite orders follow by iterating the actual derivative formula,
including Banach-valued derivatives. -/
theorem contDiff_setIntegral_of_joint_contDiff
    {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H) {K : Set ℝ} (hK : IsCompact K) :
    ContDiff ℝ ∞ (fun p => ∫ t in K, H (p, t)) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing E with
  | zero =>
    change ContDiff ℝ 0 _
    rw [contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun p =>
      (hasFDerivAt_setIntegral_of_joint_contDiff hH hK p).continuousAt)
  | succ n ih =>
    have he : fderiv ℝ (fun p => ∫ t in K, H (p, t)) =
        fun p => ∫ t in K, fderiv ℝ (fun p => H (p, t)) p :=
      funext (fun p => (hasFDerivAt_setIntegral_of_joint_contDiff hH hK p).fderiv)
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_setIntegral_of_joint_contDiff hH hK p).differentiableAt,
      by simp, ?_⟩
    rw [he]
    exact ih (contDiff_parameter_fderiv hH)

/-- The same smoothness result for a fixed oriented time interval. -/
theorem contDiff_intervalIntegral_of_joint_contDiff
    {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : P × ℝ → E} (hH : ContDiff ℝ ∞ H) (a b : ℝ) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, H (p, t)) := by
  have he : (fun p => ∫ t in a..b, H (p, t)) =
      fun p => (if a ≤ b then (1 : ℝ) else -1) • ∫ t in uIcc a b, H (p, t) := by
    funext p
    rcases le_total a b with hab | hba
    · simp only [if_pos hab, one_smul, uIcc_of_le hab]
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    · rw [intervalIntegral.integral_symm]
      by_cases hab : a ≤ b
      · have heq : a = b := le_antisymm hab hba
        subst b
        simp
      · simp only [if_neg hab, neg_smul, one_smul, uIcc_of_ge hba]
        rw [intervalIntegral.integral_of_le hba, integral_Icc_eq_integral_Ioc]
  rw [he]
  exact (contDiff_setIntegral_of_joint_contDiff hH isCompact_uIcc).const_smul _

end PlanarNikodym
