import PlanarNikodym.Geometry.WeierstrassSequence
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! Actual convergent evaluation of bounded coefficient sequences.
The evaluation map is jointly analytic in the Banach coefficient variable
and the scalar variable throughout the open unit interval. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace PlanarNikodym

def weierstrassSeriesEval (a : WeierstrassSeries) (t : ℝ) : ℝ :=
  ∑' n : ℕ, a n * t ^ n

theorem summable_weierstrassSeriesEval (a : WeierstrassSeries) {t : ℝ}
    (ht : |t| < 1) : Summable (fun n : ℕ => a n * t ^ n) := by
  have hs : Summable (fun n : ℕ => |t| ^ n) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using ht)
  apply (hs.mul_left ‖a‖).of_norm_bounded
  intro n
  simpa only [norm_mul, norm_pow, Real.norm_eq_abs] using mul_le_mul_of_nonneg_right
    (lp.norm_apply_le_norm ENNReal.top_ne_zero a n) (pow_nonneg (abs_nonneg t) n)

@[simp]
theorem weierstrassSeriesEval_zero (a : WeierstrassSeries) :
    weierstrassSeriesEval a 0 = a 0 := by
  rw [weierstrassSeriesEval, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

@[simp]
theorem weierstrassSeriesEval_zero_series (t : ℝ) :
    weierstrassSeriesEval 0 t = 0 := by
  simp [weierstrassSeriesEval]

private def coefficientFunctional (n : ℕ) : WeierstrassSeries →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : ℕ => ℝ) ∞ n

@[simp]
private theorem coefficientFunctional_apply (n : ℕ) (a : WeierstrassSeries) :
    coefficientFunctional n a = a n := rfl

private theorem norm_coefficientFunctional_le (n : ℕ) :
    ‖coefficientFunctional n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero a n

private def evaluationPowerSeries :
    FormalMultilinearSeries ℝ ℝ (WeierstrassSeries →L[ℝ] ℝ) :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (coefficientFunctional n)

private theorem evaluationPowerSeries_radius :
    1 ≤ evaluationPowerSeries.radius := by
  apply evaluationPowerSeries.le_radius_of_bound 1 (r := 1)
  intro n
  simpa [evaluationPowerSeries] using norm_coefficientFunctional_le n

private theorem evaluationPowerSeries_mem {t : ℝ} (ht : |t| < 1) :
    t ∈ Metric.eball 0 evaluationPowerSeries.radius := by
  apply lt_of_lt_of_le _ evaluationPowerSeries_radius
  simpa [edist_dist, Real.dist_eq] using (ENNReal.ofReal_lt_one.mpr ht)

private theorem evaluationPowerSeries_apply {t : ℝ} (ht : |t| < 1)
    (a : WeierstrassSeries) :
    evaluationPowerSeries.sum t a = weierstrassSeriesEval a t := by
  have hs := ((ContinuousLinearMap.apply ℝ ℝ) a).hasSum
    (evaluationPowerSeries.summable (evaluationPowerSeries_mem ht)).hasSum
  simpa [weierstrassSeriesEval, FormalMultilinearSeries.sum, evaluationPowerSeries,
    ContinuousMultilinearMap.mkPiRing_apply,
    Finset.prod_const, smul_eq_mul, mul_comm] using hs.tsum_eq.symm

/-- Genuine joint analyticity, with the coefficient variable in the
Banach space `ℓ∞`; this is stronger than separate scalar analyticity. -/
theorem analyticAt_weierstrassSeriesEval (a : WeierstrassSeries) {t : ℝ}
    (ht : |t| < 1) :
    AnalyticAt ℝ (fun z : WeierstrassSeries × ℝ => weierstrassSeriesEval z.1 z.2) (a, t) := by
  have he : AnalyticAt ℝ evaluationPowerSeries.sum t :=
    evaluationPowerSeries.analyticOnNhd t (evaluationPowerSeries_mem ht)
  have hb : AnalyticAt ℝ
      (fun z : (WeierstrassSeries →L[ℝ] ℝ) × WeierstrassSeries => z.1 z.2)
      (evaluationPowerSeries.sum t, a) :=
    (ContinuousLinearMap.id ℝ (WeierstrassSeries →L[ℝ] ℝ)).analyticAt_bilinear _
  have he' : AnalyticAt ℝ
      (fun z : WeierstrassSeries × ℝ => evaluationPowerSeries.sum z.2) (a, t) :=
    AnalyticAt.comp (f := fun z : WeierstrassSeries × ℝ => z.2) (x := (a, t))
      he analyticAt_snd
  have hjoint : AnalyticAt ℝ
      (fun z : WeierstrassSeries × ℝ => evaluationPowerSeries.sum z.2 z.1) (a, t) :=
    hb.comp₂ he' analyticAt_fst
  apply hjoint.congr
  have hnear : ∀ᶠ z : WeierstrassSeries × ℝ in 𝓝 (a, t), |z.2| < 1 :=
    (isOpen_lt (continuous_snd.abs) continuous_const).mem_nhds ht
  filter_upwards [hnear] with z hz
  exact evaluationPowerSeries_apply hz z.1

/-- Evaluation of an actual Banach-valued analytic coefficient germ. -/
theorem AnalyticAt.weierstrassSeriesEval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : E → WeierstrassSeries} {t : E → ℝ} {x : E}
    (ha : AnalyticAt ℝ a x) (ht : AnalyticAt ℝ t x) (hsmall : |t x| < 1) :
    AnalyticAt ℝ (fun y => weierstrassSeriesEval (a y) (t y)) x :=
  (analyticAt_weierstrassSeriesEval (a x) hsmall).comp₂ ha ht

theorem weierstrassSeriesEval_add (a b : WeierstrassSeries) {t : ℝ} (ht : |t| < 1) :
    weierstrassSeriesEval (a + b) t =
      weierstrassSeriesEval a t + weierstrassSeriesEval b t := by
  simpa [weierstrassSeriesEval, add_mul] using
    (summable_weierstrassSeriesEval a ht).tsum_add (summable_weierstrassSeriesEval b ht)

theorem weierstrassSeriesEval_smul (c : ℝ) (a : WeierstrassSeries) (t : ℝ) :
    weierstrassSeriesEval (c • a) t = c * weierstrassSeriesEval a t := by
  simp only [weierstrassSeriesEval, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem weierstrassSeriesEval_sum {ι : Type*} (s : Finset ι)
    (a : ι → WeierstrassSeries) {t : ℝ} (ht : |t| < 1) :
    weierstrassSeriesEval (∑ i ∈ s, a i) t = ∑ i ∈ s, weierstrassSeriesEval (a i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, weierstrassSeriesEval_add _ _ ht, ih]

theorem weierstrassSeriesEval_single (n : ℕ) (c t : ℝ) :
    weierstrassSeriesEval (lp.single ∞ n c) t = c * t ^ n := by
  rw [weierstrassSeriesEval, tsum_eq_single n]
  · simp
  · intro m hm
    simp [lp.single_apply, Pi.single_eq_of_ne hm]

/-- Multiplication by `X^m` agrees with the actual scalar power series. -/
theorem weierstrassSeriesEval_shift (m : ℕ) (a : WeierstrassSeries)
    {t : ℝ} (ht : |t| < 1) :
    weierstrassSeriesEval (weierstrassShift m a) t = t ^ m * weierstrassSeriesEval a t := by
  have h := (summable_weierstrassSeriesEval (weierstrassShift m a) ht).sum_add_tsum_nat_add m
  have hz : ∑ i ∈ Finset.range m, weierstrassShift m a i * t ^ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [weierstrassShift_apply_lt a (Finset.mem_range.mp hi), zero_mul]
  rw [hz, zero_add] at h
  calc
    weierstrassSeriesEval (weierstrassShift m a) t =
        ∑' n, weierstrassShift m a (n + m) * t ^ (n + m) := h.symm
    _ = ∑' n, t ^ m * (a n * t ^ n) := by
      apply tsum_congr
      intro n
      rw [weierstrassShift_apply_add, pow_add]
      ring
    _ = t ^ m * weierstrassSeriesEval a t := tsum_mul_left

/-- Evaluation of the finite head and shifted tail. -/
theorem weierstrassSeriesEval_glue (m : ℕ) (a : Fin m → ℝ)
    (u : WeierstrassSeries) {t : ℝ} (ht : |t| < 1) :
    weierstrassSeriesEval (weierstrassGlue m (a, u)) t =
      (∑ i : Fin m, a i * t ^ (i : ℕ)) + t ^ m * weierstrassSeriesEval u t := by
  rw [weierstrassGlue_eq, weierstrassSeriesEval_add _ _ ht,
    weierstrassSeriesEval_sum _ _ ht, weierstrassSeriesEval_shift _ _ ht]
  simp [weierstrassSeriesEval_smul, weierstrassSeriesEval_single]

/-- The bounded-sequence preparation equation is an actual scalar
factorization throughout the disk of convergence. -/
theorem weierstrassSeriesEval_preparation (m : ℕ) (a : Fin m → ℝ)
    (u : WeierstrassSeries) {t : ℝ} (ht : |t| < 1) :
    weierstrassSeriesEval
      (weierstrassShift m u + ∑ i : Fin m, a i • weierstrassShift (i : ℕ) u) t =
      (t ^ m + ∑ i : Fin m, a i * t ^ (i : ℕ)) * weierstrassSeriesEval u t := by
  rw [weierstrassSeriesEval_add _ _ ht, weierstrassSeriesEval_shift _ _ ht,
    weierstrassSeriesEval_sum _ _ ht, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [weierstrassSeriesEval_smul, weierstrassSeriesEval_shift _ _ ht]
  ring

/-- Shrink the scalar radius without leaving the Banach sequence space. -/
def weierstrassRescale (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    WeierstrassSeries →L[ℝ] WeierstrassSeries :=
  LinearMap.mkContinuous
    { toFun := fun u =>
        ⟨fun n => ρ ^ n * u n, memℓp_infty ⟨‖u‖, by
          rintro _ ⟨n, rfl⟩
          calc
            ‖ρ ^ n * u n‖ = |ρ| ^ n * ‖u n‖ := by rw [norm_mul, norm_pow, Real.norm_eq_abs]
            _ ≤ 1 * ‖u‖ := mul_le_mul
              (pow_le_one₀ (abs_nonneg ρ) hρ) (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)
              (norm_nonneg _) zero_le_one
            _ = ‖u‖ := one_mul _⟩⟩
      map_add' := fun u v => by ext n; exact mul_add _ _ _
      map_smul' := fun c u => by ext n; change ρ ^ n * (c * u n) = c * (ρ ^ n * u n); ring }
    1 (fun u => by
      simp only [one_mul]
      apply lp.norm_le_of_forall_le (norm_nonneg u)
      intro n
      change ‖ρ ^ n * u n‖ ≤ ‖u‖
      calc
        ‖ρ ^ n * u n‖ = |ρ| ^ n * ‖u n‖ := by rw [norm_mul, norm_pow, Real.norm_eq_abs]
        _ ≤ 1 * ‖u‖ := mul_le_mul
          (pow_le_one₀ (abs_nonneg ρ) hρ) (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)
          (norm_nonneg _) zero_le_one
        _ = ‖u‖ := one_mul _)

@[simp]
theorem weierstrassRescale_apply (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (u : WeierstrassSeries) (n : ℕ) :
    weierstrassRescale ρ hρ u n = ρ ^ n * u n := rfl

theorem weierstrassSeriesEval_rescale (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (u : WeierstrassSeries) (t : ℝ) :
    weierstrassSeriesEval (weierstrassRescale ρ hρ u) t =
      weierstrassSeriesEval u (ρ * t) := by
  apply tsum_congr
  intro n
  rw [weierstrassRescale_apply, mul_pow]
  ring

end PlanarNikodym
