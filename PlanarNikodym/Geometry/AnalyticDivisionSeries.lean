import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Convergent multilinear series for division by a coordinate

The coefficients below telescope the difference between a power series at `(x,t)` and at
`(x,0)`. Their norm is bounded by `(n+1) ‖p (n+1)‖`; thus the construction preserves a positive
convergence radius. This is an analytic construction, not division of formal adic series.
-/

noncomputable section
open scoped Topology ENNReal NNReal
open Filter Set

namespace PlanarNikodym

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The projection onto the parameter hyperplane. -/
def analyticDivisionProjection : E × ℝ →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod 0

@[simp]
theorem analyticDivisionProjection_apply (z : E × ℝ) :
    analyticDivisionProjection z = (z.1, 0) := rfl

theorem norm_analyticDivisionProjection_le :
    ‖analyticDivisionProjection (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [analyticDivisionProjection_apply, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _),
    one_mul]
  exact le_max_left _ _

/-- The maps in a telescoping term: identity before the distinguished slot and projection
after it. -/
def analyticDivisionSlot {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    E × ℝ →L[ℝ] E × ℝ :=
  if i.succAbove j < i then ContinuousLinearMap.id ℝ (E × ℝ)
  else analyticDivisionProjection

theorem norm_analyticDivisionSlot_le {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    ‖analyticDivisionSlot (E := E) i j‖ ≤ 1 := by
  unfold analyticDivisionSlot
  split_ifs
  · exact ContinuousLinearMap.norm_id_le
  · exact norm_analyticDivisionProjection_le

/-- One homogeneous coefficient of the convergent Hadamard quotient. -/
def analyticDivisionSeries (p : FormalMultilinearSeries ℝ (E × ℝ) F) :
    FormalMultilinearSeries ℝ (E × ℝ) F :=
  fun n => ∑ i : Fin (n + 1),
    ((p (n + 1)).curryMid i (0, 1)).compContinuousLinearMap
      (analyticDivisionSlot i)

theorem norm_analyticDivisionSeries_le
    (p : FormalMultilinearSeries ℝ (E × ℝ) F) (n : ℕ) :
    ‖analyticDivisionSeries p n‖ ≤ (n + 1 : ℝ) * ‖p (n + 1)‖ := by
  unfold analyticDivisionSeries
  calc
    _ ≤ ∑ i : Fin (n + 1),
        ‖((p (n + 1)).curryMid i (0, 1)).compContinuousLinearMap
          (analyticDivisionSlot i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n + 1), ‖p (n + 1)‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖(p (n + 1)).curryMid i (0, 1)‖ *
            ∏ j : Fin n, ‖analyticDivisionSlot (E := E) i j‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖p (n + 1)‖ * 1 := by
          apply mul_le_mul
          · simpa using ((p (n + 1)).curryMid i).le_opNorm (0, 1)
          · exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
              (fun j _ => norm_analyticDivisionSlot_le i j)
          · positivity
          · positivity
        _ = _ := mul_one _
    _ = _ := by simp

/-- Algebraic identity for one homogeneous term. -/
theorem smul_analyticDivisionSeries_apply
    (p : FormalMultilinearSeries ℝ (E × ℝ) F) (n : ℕ) (z : E × ℝ) :
    z.2 • analyticDivisionSeries p n (fun _ => z) =
      p (n + 1) (fun _ => z) -
        p (n + 1) (fun _ => analyticDivisionProjection z) := by
  classical
  have ht := MultilinearMap.map_sub_map_piecewise
    (p (n + 1)).toMultilinearMap (fun _ => z)
    (fun _ => analyticDivisionProjection z) Finset.univ
  simp only [Finset.piecewise_univ, Finset.mem_univ, true_implies] at ht
  change p (n + 1) (fun _ => z) - p (n + 1) (fun _ => analyticDivisionProjection z) = _ at ht
  rw [ht]
  simp only [analyticDivisionSeries, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ← ContinuousMultilinearMap.smul_apply, ← map_smul,
    ContinuousMultilinearMap.curryMid_apply]
  change (p (n + 1)) _ = (p (n + 1)) _
  apply congrArg (p (n + 1))
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp only [lt_self_iff_false, if_false, if_true]
    ext <;> simp
  · funext j
    simp only [Fin.removeNth, analyticDivisionSlot]
    by_cases h : i.succAbove j < i
    · simp [h]
    · simp [h, Fin.ne_succAbove]

/-- Division by the last coordinate preserves a positive analytic convergence radius. -/
theorem analyticDivisionSeries_radius_pos
    (p : FormalMultilinearSeries ℝ (E × ℝ) F) (hp : 0 < p.radius) :
    0 < (analyticDivisionSeries p).radius := by
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨a, ha, C, hC, hbound⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius hr
  have hs : Summable (fun n : ℕ => (n + 1 : ℝ) * a ^ (n + 1)) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := a) 1
      (by simpa [Real.norm_eq_abs, abs_of_pos ha.1] using ha.2)
    simpa using (summable_nat_add_iff 1).mpr h
  have hqr : (r : ℝ≥0∞) ≤ (analyticDivisionSeries p).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    apply Summable.of_nonneg_of_le (fun n => by positivity)
      (f := fun n : ℕ => (C / r) * ((n + 1 : ℝ) * a ^ (n + 1)))
    · intro n
      calc
        ‖analyticDivisionSeries p n‖ * (r : ℝ) ^ n ≤
            ((n + 1 : ℝ) * ‖p (n + 1)‖) * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (norm_analyticDivisionSeries_le p n) (by positivity)
        _ = ((n + 1 : ℝ) / r) * (‖p (n + 1)‖ * (r : ℝ) ^ (n + 1)) := by
          rw [pow_succ]
          field_simp
        _ ≤ ((n + 1 : ℝ) / r) * (C * a ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left (hbound (n + 1)) (by positivity)
        _ = _ := by ring
    · exact hs.mul_left _
  exact hr0.trans_le hqr

variable [CompleteSpace F]

/-- Parameter-dependent Hadamard division. The quotient is analytic jointly in the parameter
and the last coordinate, rather than merely analytic on each individual slice. -/
theorem exists_analytic_coordinate_quotient
    (f : E × ℝ → F) (x₀ : E) (t₀ : ℝ) (hf : AnalyticAt ℝ f (x₀, t₀)) :
    ∃ q : E × ℝ → F, AnalyticAt ℝ q (x₀, t₀) ∧
      ∀ᶠ z in 𝓝 (x₀, t₀), f z - f (z.1, t₀) = (z.2 - t₀) • q z := by
  obtain ⟨p, hp⟩ := hf
  let q := analyticDivisionSeries p
  have hq : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall (analyticDivisionSeries_radius_pos p hp.radius_pos)
  have hproj : Tendsto (analyticDivisionProjection (E := E)) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using
      (analyticDivisionProjection (E := E)).continuous.tendsto (0 : E × ℝ)
  have heq : ∀ᶠ z in 𝓝 (0 : E × ℝ),
      f ((x₀, t₀) + z) - f ((x₀, t₀) + analyticDivisionProjection z) =
        z.2 • q.sum z := by
    filter_upwards [hp.eventually_hasSum, hproj.eventually hp.eventually_hasSum,
      hq.eventually_hasSum] with z hz hPz hqz
    have hzero : p 0 (fun _ => z) = p 0 (fun _ => analyticDivisionProjection z) :=
      congrArg (p 0) (funext fun i => Fin.elim0 i)
    have htail := (hasSum_nat_add_iff' 1).mpr (hz.sub hPz)
    simp only [Finset.sum_range_one, hzero, sub_self, sub_zero] at htail
    have hdiv := hqz.const_smul z.2
    simp only [zero_add] at hdiv
    have hdiv' : HasSum
        (fun n => p (n + 1) (fun _ => z) -
          p (n + 1) (fun _ => analyticDivisionProjection z))
        (z.2 • q.sum z) := by
      convert hdiv using 1
      funext n
      exact (smul_analyticDivisionSeries_apply p n z).symm
    exact htail.unique hdiv'
  refine ⟨fun z => q.sum (z - (x₀, t₀)), ?_, ?_⟩
  · simpa only [zero_add] using hq.analyticAt.comp_sub (x₀, t₀)
  · have ht : Tendsto (fun z : E × ℝ => z - (x₀, t₀))
        (𝓝 (x₀, t₀)) (𝓝 0) := by
      simpa only [id_eq, sub_self] using
        (continuous_id.sub continuous_const : Continuous
          (fun z : E × ℝ => z - (x₀, t₀))).tendsto (x₀, t₀)
    filter_upwards [ht.eventually heq] with z hz
    simpa only [add_sub_cancel, Prod.snd_sub, analyticDivisionProjection_apply,
      Prod.fst_sub, Prod.mk_add_mk, add_sub_cancel_left, add_zero] using hz

end PlanarNikodym
