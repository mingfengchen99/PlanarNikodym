import PlanarNikodym.Analysis.Maximal.AnalysisClassification
import PlanarNikodym.Examples.P5Examples

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym.Examples

/-- A positive budget for both analytic losses always exists at finite p. -/
theorem admissible_analysis_losses (p : ℝ≥0) (hp : 0 < p) :
    0 < 1 / (4 * (p : ℝ)) ∧
    1 / (4 * (p : ℝ)) + 1 / (4 * (p : ℝ)) < 1 / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := hp
  constructor
  · positivity
  · field_simp
    nlinarith

/-- For d=1, the local-smoothing threshold is p=6. Splitting a loss of
1/12 into 1/24+1/24 leaves the summable decay 2^(-k/12). -/
theorem one_aux_frequency_budget :
    smoothingThreshold 1 = 6 ∧
    (-((1 + 1 : ℕ) : ℝ) / 6 + 1 / 24) + (1 / 6 + 1 / 24) = -(1 / 12 : ℝ) ∧
    (∑' k, dyadicWeight (-(1 / 12 : ℝ)) k) < ∞ := by
  refine ⟨by norm_num [smoothingThreshold], by norm_num, ?_⟩
  exact dyadicWeight_tsum_lt_top (by norm_num)

/-- A Borel plane-null indicator can have a positive time average on a
specific curve. This verifies why reconstruction must concern pointwise
values, even though the ambient `Lp` seminorm is zero. -/
theorem null_indicator_positive_on_its_curve {d : ℕ} (G : Family 2 d)
    (hs : G.IsSmooth) (q : Parameters 2 d) (hq : q ∈ G.W) (p : ℝ≥0) (hp : p ≠ 0) :
    eLpNorm ((G.curve q).indicator (fun _ => (1 : ℂ))) p volume = 0 ∧
    0 < G.positiveAverage ((G.curve q).indicator (fun _ => 1)) q := by
  have hm := (G.curve_isCompact hs q hq).measurableSet
  constructor
  · have hpR : 0 < (p : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hp)
    rw [eLpNorm_indicator_const hm (by exact_mod_cast hp : (p : ℝ≥0∞) ≠ 0)
      ENNReal.coe_ne_top, G.curve_volume_zero hs q hq]
    simp only [enorm_one, one_mul, ENNReal.coe_toReal]
    exact ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpR)
  · have he : G.hitTimes q (G.curve q) = G.I.carrier := by
      ext t
      exact ⟨fun ht => ht.1, fun ht => ⟨ht, mem_image_of_mem _ ht⟩⟩
    rw [G.positiveAverage_indicator q (G.curve q) (by rw [he]; exact measurableSet_Icc), he]
    change 0 < volume (Icc G.I.left G.I.right)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr G.I.nondegenerate)

theorem affineGraphs_no_nikodym_from_analysis (hB : BocherInput)
    (hA : CinematicAnalysisInput) (I : Interval) : ¬ (affineGraphs I).AdmitsNikodym :=
  affineGraphs_no_nikodym hB (cinematicNullInput_of_analysis hA) I

end PlanarNikodym.Examples
