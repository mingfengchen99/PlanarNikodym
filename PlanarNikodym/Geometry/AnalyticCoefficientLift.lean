import PlanarNikodym.Geometry.AnalyticCoefficientSeries
import Mathlib.Analysis.Analytic.Constructions

/-! Actual Banach-analytic coefficient lifting of a joint analytic germ.
The coefficient series converges in the supremum norm, not only coordinatewise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ENNReal NNReal Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticCoefficientSeries_sum_apply
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hb : ∀ n, ‖p n‖ ≤ C / R ^ n)
    (hp : 0 < p.radius) :
    ∀ᶠ x in 𝓝 (0 : E), ∀ n,
      (analyticCoefficientSeries p R C hR hC hb).sum x n =
        p.changeOrigin (x, 0) n (fun _ => (0, R / 2)) := by
  let Q := analyticCoefficientSeries p R C hR hC hb
  have hQ := Q.hasFPowerSeriesOnBall (analyticCoefficientSeries_radius_pos p R C hR hC hb)
  have hball : ∀ᶠ x in 𝓝 (0 : E), (x, (0 : ℝ)) ∈ Metric.eball 0 p.radius := by
    have ht : Tendsto (fun x : E => (x, (0 : ℝ))) (𝓝 0) (𝓝 0) := by
      change Tendsto _ _ (𝓝 ((0 : E), (0 : ℝ)))
      exact (continuous_id.prodMk continuous_const).tendsto (0 : E)
    exact ht.eventually (Metric.eball_mem_nhds 0 hp)
  filter_upwards [hQ.eventually_hasSum, hball] with x hx hxp
  intro n
  have hl := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) ∞ n).hasSum hx
  have hr := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E × ℝ) ℝ
      (fun _ => (0, R / 2))).hasSum
    ((p.hasFPowerSeriesOnBall_changeOrigin n hp).hasSum hxp)
  have hr' : HasSum (fun k => Q k (fun _ => x) n)
      (p.changeOrigin (x, 0) n (fun _ => (0, R / 2))) := by
    simp only [zero_add] at hr
    convert hr using 1 <;> simp only [Q, analyticCoefficientSeries_apply] <;> rfl
  convert hl.unique hr' using 1
  simp only [zero_add]
  rfl

theorem analyticCoefficientSeries_hasSum
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hb : ∀ n, ‖p n‖ ≤ C / R ^ n)
    (hp : 0 < p.radius) :
    ∀ᶠ z in 𝓝 (0 : E × ℝ),
      HasSum (fun n => (analyticCoefficientSeries p R C hR hC hb).sum z.1 n *
        (z.2 / (R / 2)) ^ n) (p.sum z) := by
  have hc := analyticCoefficientSeries_sum_apply p R C hR hC hb hp
  have hn : ∀ᶠ z in 𝓝 (0 : E × ℝ),
      (‖z.1‖₊ : ℝ≥0∞) + (‖z.2‖₊ : ℝ≥0∞) < p.radius := by
    have ht : Continuous (fun z : E × ℝ =>
        (‖z.1‖₊ : ℝ≥0∞) + (‖z.2‖₊ : ℝ≥0∞)) := by fun_prop
    exact ht.continuousAt.eventually_lt continuousAt_const (by simpa using hp)
  filter_upwards [continuous_fst.continuousAt.eventually hc, hn] with z hz hzn
  have hnorm : (‖(z.1, (0 : ℝ))‖₊ : ℝ≥0∞) +
      (‖((0 : E), z.2)‖₊ : ℝ≥0∞) < p.radius := by
    simpa [Prod.nnnorm_def] using hzn
  have ht : ((0 : E), z.2) ∈ Metric.eball 0 (p.changeOrigin (z.1, 0)).radius := by
    apply mem_eball_zero_iff.mpr
    apply lt_of_lt_of_le _ p.changeOrigin_radius
    rw [lt_tsub_iff_right]
    simpa [add_comm, enorm_eq_nnnorm] using hnorm
  have hs := (p.changeOrigin (z.1, 0)).hasSum ht
  rw [p.changeOrigin_eval hnorm] at hs
  have heq (n : ℕ) : (p.changeOrigin (z.1, 0) n) (fun _ => (0, z.2)) =
      (analyticCoefficientSeries p R C hR hC hb).sum z.1 n * (z.2 / (R / 2)) ^ n := by
    rw [hz n]
    have hv : (fun _ : Fin n => ((0 : E), z.2)) =
        fun _ => (z.2 / (R / 2)) • ((0 : E), R / 2) := by
      funext i
      ext <;> simp [div_mul_cancel₀ _ (show R / 2 ≠ 0 by positivity)]
    rw [hv, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simpa only [heq, Prod.mk_add_mk, add_zero, zero_add] using hs

/-- Every joint real analytic germ has an actual bounded coefficient family,
analytic in the parameter in the Banach norm, on a rescaled vertical disk. -/
theorem exists_analytic_coefficient_lift (f : E × ℝ → ℝ) (x₀ : E) (t₀ : ℝ)
    (hf : AnalyticAt ℝ f (x₀, t₀)) :
    ∃ s > 0, ∃ F : E → lp (fun _ : ℕ => ℝ) ∞,
      AnalyticAt ℝ F x₀ ∧
      ∀ᶠ z in 𝓝 (x₀, t₀), HasSum
        (fun n => F z.1 n * ((z.2 - t₀) / s) ^ n) (f z) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.radius_pos
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨C, hC, hb⟩ := p.norm_le_div_pow_of_pos_of_lt_radius
    (show 0 < r by exact_mod_cast hr0) hr
  let Q := analyticCoefficientSeries p r C hrpos hC.le hb
  have hQ := Q.hasFPowerSeriesOnBall (analyticCoefficientSeries_radius_pos p r C hrpos hC.le hb)
  refine ⟨r / 2, by positivity, fun x => Q.sum (x - x₀), ?_, ?_⟩
  · simpa only [zero_add] using hQ.analyticAt.comp_sub x₀
  · have hs := analyticCoefficientSeries_hasSum p r C hrpos hC.le hb hp.radius_pos
    have ht : Tendsto (fun z : E × ℝ => z - (x₀, t₀)) (𝓝 (x₀, t₀)) (𝓝 0) := by
      simpa using (continuous_id.sub continuous_const : Continuous
        (fun z : E × ℝ => z - (x₀, t₀))).tendsto (x₀, t₀)
    have hpEq : ∀ᶠ z in 𝓝 (x₀, t₀), p.sum (z - (x₀, t₀)) = f z := by
      filter_upwards [hp.eventually_hasSum_sub] with z hz
      exact hz.tsum_eq
    filter_upwards [ht.eventually hs, hpEq] with z hz he
    simpa only [Q, Prod.fst_sub, Prod.snd_sub, he] using hz

end PlanarNikodym
