import PlanarNikodym.Geometry.WeierstrassBanachDivision
import PlanarNikodym.Geometry.AnalyticSequenceEvaluation
import PlanarNikodym.Geometry.AnalyticCoefficientUniqueness

/-! A true scalar division identity determines the corresponding bounded
coefficient equation. No formal coefficient identity or uniform analytic
radius of the quotient is assumed. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace PlanarNikodym

theorem weierstrassDivisionOperator_eval (m : ℕ) (a r : Fin m → ℝ)
    (Q : WeierstrassSeries) {t : ℝ} (ht : |t| < 1) :
    weierstrassSeriesEval (weierstrassDivisionOperator m a (r, Q)) t =
      (∑ i : Fin m, r i * t ^ (i : ℕ)) +
        (t ^ m + ∑ i : Fin m, a i * t ^ (i : ℕ)) * weierstrassSeriesEval Q t := by
  rw [weierstrassDivisionOperator_apply, weierstrassSeriesEval_add _ _ ht,
    weierstrassSeriesEval_sum _ _ ht]
  simp only [weierstrassSeriesEval_smul, weierstrassSeriesEval_single, one_mul,
    weierstrassPolynomialAction, weierstrassSeriesEval_preparation _ _ _ ht]

/-- Recover the actual sequence equation from a scalar germ identity,
using its independently rescaled convergent quotient series. The scale
need only be nonzero, and the degree may be zero. -/
theorem weierstrassDivisionOperator_eq_zero_of_scalar_identity
    (m : ℕ) (a r : Fin m → ℝ) (Q : WeierstrassSeries) (t₀ s : ℝ)
    (hs : s ≠ 0) (q : ℝ → ℝ)
    (hsum : ∀ᶠ t in 𝓝 t₀,
      HasSum (fun n : ℕ => Q n * ((t - t₀) / s) ^ n) (q t))
    (heq : ∀ᶠ t in 𝓝 t₀,
      q t * ((t - t₀) ^ m + ∑ i : Fin m, a i * (t - t₀) ^ (i : ℕ)) +
        ∑ i : Fin m, r i * (t - t₀) ^ (i : ℕ) = 0) :
    weierstrassDivisionOperator m (fun i => a i * s ^ (i : ℕ) / s ^ m)
      (fun i => r i * s ^ (i : ℕ), s ^ m • Q) = 0 := by
  apply lp_eq_of_eventually_powerSeries_eq
  have hchange : Tendsto (fun t : ℝ => t₀ + s * t) (𝓝 0) (𝓝 t₀) := by
    have hc : Continuous (fun t : ℝ => t₀ + s * t) := by fun_prop
    simpa only [mul_zero, add_zero] using hc.tendsto (0 : ℝ)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 :=
    continuousAt_id.abs.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [hchange.eventually hsum, hchange.eventually heq, hsmall]
    with t hsumt heqt ht
  change weierstrassSeriesEval
      (weierstrassDivisionOperator m (fun i => a i * s ^ (i : ℕ) / s ^ m)
        (fun i => r i * s ^ (i : ℕ), s ^ m • Q)) t = weierstrassSeriesEval 0 t
  have heval : weierstrassSeriesEval Q t = q (t₀ + s * t) := by
    simpa only [weierstrassSeriesEval, add_sub_cancel_left, mul_div_cancel_left₀ t hs]
      using hsumt.tsum_eq
  have hpoly :
      (t ^ m + ∑ i : Fin m, (a i * s ^ (i : ℕ) / s ^ m) * t ^ (i : ℕ)) * s ^ m =
        (s * t) ^ m + ∑ i : Fin m, a i * (s * t) ^ (i : ℕ) := by
    rw [add_mul, Finset.sum_mul, mul_pow]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow]
      field_simp
  have hrem : (∑ i : Fin m, (r i * s ^ (i : ℕ)) * t ^ (i : ℕ)) =
      ∑ i : Fin m, r i * (s * t) ^ (i : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow]
    ring
  rw [weierstrassDivisionOperator_eval _ _ _ _ ht, weierstrassSeriesEval_smul, heval,
    ← mul_assoc, hpoly, hrem, weierstrassSeriesEval_zero_series]
  simpa only [add_sub_cancel_left, add_comm, mul_comm] using heqt

end PlanarNikodym
