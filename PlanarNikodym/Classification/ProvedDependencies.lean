import PlanarNikodym.Rank.WronskianCriterion
import PlanarNikodym.Rank.RankRegularity
import PlanarNikodym.Analysis.Maximal.AnalysisClassification

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- The full-rank finite-exception theorem no longer requires a Bôcher
argument from the caller. -/
theorem full_curve_rank_cinematic_exceptions_finite_proved {d : ℕ}
    (G : Family 2 d) (ha : G.IsAnalytic) (p : Parameters 2 d) (hp : p ∈ G.W)
    (hc : G.curveRank p = d + 2) :
    {t | t ∈ G.I.carrier ∧ G.cinematicDet (t, p) = 0}.Finite :=
  full_curve_rank_cinematic_exceptions_finite bocher_input G ha p hp hc

theorem maximal_gap_incidence_null_from_analysis (hA : CinematicAnalysisInput)
    {d m : ℕ} (G : Family 2 d) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G m (m + 2)) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 :=
  maximal_gap_incidence_null bocher_input (cinematicNullInput_of_analysis hA) G hW ha hr

/-- Legacy three-field input after eliminating Bôcher. Scalar avoidance
is now proved in `ProvedAvoidance`; its compatibility constructor supplies
that field automatically. The smooth-test route also removes the separate
low-frequency and reconstruction obligations from the analytic package. -/
structure P8RemainingInputs : Prop where
  analysis : CinematicAnalysisInput
  projectionConstruction : ProjectionConstructionInput
  projectionAvoidance : ProjectionAvoidanceInput

theorem P8RemainingInputs.toP7 (h : P8RemainingInputs) : P7Inputs :=
  ⟨bocher_input, h.analysis, h.projectionConstruction, h.projectionAvoidance⟩

theorem theorem_1_5_after_bocher (h : P8RemainingInputs) : Theorem15Statement :=
  theorem_1_5_from_analysis h.toP7

theorem theorem_1_4_after_bocher (h : P8RemainingInputs) (geometry : TameGeometryInput) :
    Theorem14Statement :=
  theorem_1_4_from_analysis h.toP7 geometry

end PlanarNikodym
