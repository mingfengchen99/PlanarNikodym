import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Actual uniqueness of bounded power-series coefficients

A bounded coefficient sequence has convergence radius at least one. Equality
of the actual sums on a neighborhood therefore identifies the coefficients by
one-variable analytic uniqueness. The scaled version identifies the base
coefficient vector after normalizing a distinguished fiber to a monomial.
-/

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace PlanarNikodym

theorem one_le_lp_ofScalars_radius (a : lp (fun _ : ℕ => ℝ) ∞) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℝ (fun n => a n)).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ ‖a‖ (r := 1)
  intro n
  simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
    using lp.norm_apply_le_norm ENNReal.top_ne_zero a n

/-- Equality of actual sums on a neighborhood determines the entire bounded
coefficient sequence. In particular no coefficient identity is assumed. -/
theorem lp_eq_of_eventually_powerSeries_eq
    (a b : lp (fun _ : ℕ => ℝ) ∞)
    (heq : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∑' n : ℕ, a n * t ^ n) = ∑' n : ℕ, b n * t ^ n) :
    a = b := by
  let p := FormalMultilinearSeries.ofScalars ℝ (fun n => a n)
  let q := FormalMultilinearSeries.ofScalars ℝ (fun n => b n)
  have hp : 0 < p.radius := lt_of_lt_of_le zero_lt_one (one_le_lp_ofScalars_radius a)
  have hq : 0 < q.radius := lt_of_lt_of_le zero_lt_one (one_le_lp_ofScalars_radius b)
  have hs : p.sum =ᶠ[𝓝 (0 : ℝ)] q.sum := by
    filter_upwards [heq] with t ht
    simpa only [p, q, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using ht
  have hpq := (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
    |>.eq_formalMultilinearSeries_of_eventually
      (q.hasFPowerSeriesOnBall hq).hasFPowerSeriesAt hs
  have hcoeff : (fun n => a n) = fun n => b n :=
    FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ hpq
  exact lp.ext hcoeff

/-- A bounded series which actually sums to a monomial near zero is precisely
the singleton coefficient sequence of that monomial. -/
theorem lp_eq_single_of_eventually_hasSum_monomial
    (a : lp (fun _ : ℕ => ℝ) ∞) (c : ℝ) (m : ℕ)
    (hsum : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasSum (fun n : ℕ => a n * t ^ n) (c * t ^ m)) :
    a = c • lp.single ∞ m (1 : ℝ) := by
  apply lp_eq_of_eventually_powerSeries_eq
  filter_upwards [hsum] with t ht
  rw [ht.tsum_eq, tsum_eq_single m]
  · simp
  · intro n hn
    simp [lp.single_apply, Pi.single_eq_of_ne hn]

/-- A monomial centered at `t₀`, expressed using the scaled variable
`(t-t₀)/s`, has its only nonzero coefficient equal to `s^m`. -/
theorem lp_eq_single_of_scaled_monomial
    (a : lp (fun _ : ℕ => ℝ) ∞) (t₀ s : ℝ) (m : ℕ) (hs : s ≠ 0)
    (hsum : ∀ᶠ t in 𝓝 t₀,
      HasSum (fun n : ℕ => a n * ((t - t₀) / s) ^ n) ((t - t₀) ^ m)) :
    a = s ^ m • lp.single ∞ m (1 : ℝ) := by
  apply lp_eq_single_of_eventually_hasSum_monomial
  have ht : Tendsto (fun t : ℝ => t₀ + s * t) (𝓝 0) (𝓝 t₀) := by
    have hc : Continuous (fun t : ℝ => t₀ + s * t) := by fun_prop
    simpa only [mul_zero, add_zero] using
      hc.tendsto (0 : ℝ)
  filter_upwards [ht.eventually hsum] with t h
  simpa only [add_sub_cancel_left, mul_div_cancel_left₀ t hs, mul_pow] using h

variable {E : Type*} [TopologicalSpace E]

/-- The actual joint coefficient lift of a normalized analytic fiber has the
precise base value required by the Banach preparation theorem. Analyticity of
the coefficient map is not needed for this identification; actual summation
and the fiber identity already imply it. -/
theorem coefficient_lift_eq_single_of_normalized_fiber
    (f : E × ℝ → ℝ) (F : E → lp (fun _ : ℕ => ℝ) ∞)
    (x₀ : E) (t₀ s : ℝ) (m : ℕ) (hs : s ≠ 0)
    (hlift : ∀ᶠ z in 𝓝 (x₀, t₀),
      HasSum (fun n : ℕ => F z.1 n * ((z.2 - t₀) / s) ^ n) (f z))
    (hbase : ∀ᶠ t in 𝓝 t₀, f (x₀, t) = (t - t₀) ^ m) :
    F x₀ = s ^ m • lp.single ∞ m (1 : ℝ) := by
  apply lp_eq_single_of_scaled_monomial _ t₀ s m hs
  have ht : Tendsto (fun t : ℝ => (x₀, t)) (𝓝 t₀) (𝓝 (x₀, t₀)) :=
    (continuous_const.prodMk continuous_id).tendsto t₀
  filter_upwards [ht.eventually hlift, hbase] with t h hb
  simpa only [hb] using h

end PlanarNikodym
