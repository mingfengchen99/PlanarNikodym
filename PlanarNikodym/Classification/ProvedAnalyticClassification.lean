import PlanarNikodym.Analysis.Jets.ScalarJetProvedSmoothing
import PlanarNikodym.Classification.ProjectionConstructedClassification

/-! Classification after the actual analytic and projection constructions.
The constant-rank theorem has no remaining input. The other two statements
retain exactly their analytic-cell geometry premise. -/
noncomputable section
namespace PlanarNikodym

theorem theorem_1_5_proved : Theorem15Statement :=
  theorem_1_5_after_projection cinematic_smooth_analysis_input

theorem theorem_1_4_of_connected_cells (hD : ConnectedCellInput) : Theorem14Statement :=
  theorem_1_4_after_projection cinematic_smooth_analysis_input hD

theorem proposition_1_6_of_analytic_cells (hD : AnalyticCellInput) : Proposition16Statement :=
  proposition_1_6_after_projection cinematic_smooth_analysis_input hD

end PlanarNikodym
