import PlanarNikodym.Projection.ProvedProjectionConstruction
import PlanarNikodym.Analysis.Maximal.LocalizedSmoothAnalysis

/-! Classification interfaces after the scalar projection construction.

The scalar construction and avoidance arguments are supplied by actual
proofs. The analytic estimate and, where needed, analytic cell geometry
remain explicit hypotheses.
-/

noncomputable section
namespace PlanarNikodym

theorem P8RemainingInputs.of_analysis (hA : CinematicAnalysisInput) :
    P8RemainingInputs :=
  P8RemainingInputs.of_analysis_projection hA projection_construction_input

/-- The positive intermediate-rank branch has no remaining construction
or avoidance hypothesis. -/
theorem theorem_1_5_case_positive_intermediate_proved {d m : ℕ}
    (hm : 0 < m) (G : Family 2 d) (hWne : G.W.Nonempty)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hr : ConstantRanks G m (m + 1)) :
    G.AdmitsNikodym ∧ G.HasLocalCurveReuse ∧ G.LocalReuseNotCovered :=
  theorem_1_5_case_positive_intermediate projection_construction_input
    projection_avoidance_input hm G hWne hW ha hr

/-- Only the remaining analytic input is needed for the constant-rank
classification. -/
theorem theorem_1_5_after_projection (hA : CinematicSmoothAnalysisInput) :
    Theorem15Statement :=
  theorem_1_5_after_avoidance hA projection_construction_input

theorem theorem_1_4_after_projection (hA : CinematicSmoothAnalysisInput)
    (H : ConnectedCellInput) : Theorem14Statement :=
  theorem_1_4_after_avoidance hA projection_construction_input H

theorem proposition_1_6_after_projection (hA : CinematicSmoothAnalysisInput)
    (H : AnalyticCellInput) : Proposition16Statement :=
  proposition_1_6_after_avoidance hA projection_construction_input H

theorem theorem_1_5_of_pointwise_jet_smoothing_after_projection
    (H : PointwiseJetSmoothingInput) : Theorem15Statement :=
  theorem_1_5_of_pointwise_jet_smoothing H projection_construction_input

theorem theorem_1_4_of_pointwise_jet_smoothing_after_projection
    (H : PointwiseJetSmoothingInput) (hD : ConnectedCellInput) : Theorem14Statement :=
  theorem_1_4_of_pointwise_jet_smoothing H projection_construction_input hD

theorem proposition_1_6_of_pointwise_jet_smoothing_after_projection
    (H : PointwiseJetSmoothingInput) (hD : AnalyticCellInput) : Proposition16Statement :=
  proposition_1_6_of_pointwise_jet_smoothing H projection_construction_input hD

end PlanarNikodym
