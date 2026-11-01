import PlanarNikodym.Cells.ReducedGeometry
import PlanarNikodym.Examples.P5Examples
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open Set MeasureTheory
open scoped Topology Matrix
namespace PlanarNikodym.Examples

theorem sin_cos_wronskian (t : ℝ) : wronskian ![Real.sin, Real.cos] t = -1 := by
  unfold wronskian
  rw [Matrix.det_fin_two]
  change iteratedDeriv 0 Real.sin t * iteratedDeriv 1 Real.cos t -
    iteratedDeriv 0 Real.cos t * iteratedDeriv 1 Real.sin t = -1
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Real.deriv_sin, Real.deriv_cos]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem sin_cos_independent (I : Interval) :
    LinearIndependent ℝ (fun j (t : I.carrier) => ![Real.sin, Real.cos] j t) := by
  apply independent_of_wronskian_ne_zero_interior I ![Real.sin, Real.cos] ?_
    ((I.left + I.right) / 2) ⟨by linarith [I.nondegenerate], by linarith [I.nondegenerate]⟩
  · rw [sin_cos_wronskian]
    norm_num
  · intro j t _
    fin_cases j
    · exact Real.analyticAt_sin
    · exact Real.analyticAt_cos

theorem quadratic_pair_wronskian (t : ℝ) :
    wronskian ![(fun _ : ℝ => 1), (fun x : ℝ => x ^ 2)] t = 2 * t := by
  simp [wronskian, Matrix.det_fin_two, iteratedDeriv_one]

/-- An independent analytic pair can have a singular Wronskian at an
isolated time; Bôcher does not assert nonvanishing at every time. -/
theorem quadratic_pair_has_one_exception :
    let I : Interval := ⟨-1, 1, by norm_num⟩
    let f : Fin 2 → ℝ → ℝ := ![(fun _ => 1), (fun x => x ^ 2)]
    LinearIndependent ℝ (fun j (t : I.carrier) => f j t) ∧
      {t | t ∈ I.carrier ∧ wronskian f t = 0} = {0} := by
  dsimp only
  let I : Interval := ⟨-1, 1, by norm_num⟩
  let f : Fin 2 → ℝ → ℝ := ![(fun _ => 1), (fun x => x ^ 2)]
  constructor
  · apply independent_of_wronskian_ne_zero_interior I f ?_ (1 / 2) (by norm_num [I])
    · rw [quadratic_pair_wronskian]
      norm_num
    · intro j t _
      fin_cases j
      · exact analyticAt_const
      · exact analyticAt_id.pow 2
  · ext t
    simp [Interval.carrier, quadratic_pair_wronskian]
    intro h; subst t; norm_num

theorem affineGraphs_no_nikodym_after_bocher (hA : CinematicAnalysisInput) (I : Interval) :
    ¬ (affineGraphs I).AdmitsNikodym :=
  affineGraphs_no_nikodym bocher_input (cinematicNullInput_of_analysis hA) I

theorem analytic_centers_all_aux (d : ℕ) (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (β : Set Plane) :
    IsSigmaCompact (G.centersOf β) ∧ MeasurableSet (G.centersOf β) :=
  ⟨G.centers_isSigmaCompact hW
    (fun t ht p hp => (G.parameter_analytic ha p hp ⟨t, ht⟩).continuousAt.continuousWithinAt) β,
    G.centers_measurable_of_analytic hW ha β⟩

end PlanarNikodym.Examples
