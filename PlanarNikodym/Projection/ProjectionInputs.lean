import PlanarNikodym.Projection.ProjectionModel
import PlanarNikodym.Classification.FullRankClassification

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- The scalar projection construction needed by §7.3, Steps 4–5.
Its actual proof is `projection_construction_input` in
`ProvedProjectionConstruction`: Wisewell's local construction handles the
stationary branch, and finite nonlinear blinds with a compact limit handle
the other branch. The original quantified interface is retained here. -/
def ProjectionConstructionInput : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ D : ProjectionModel d,
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E)

/-- The scalar avoidance statement used by §7.3, Step 3. Its full proof is
`projection_avoidance_input` in `ProvedAvoidance`, including positive inner
measure for every countable family of smooth fields. -/
def ProjectionAvoidanceInput : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (D : ProjectionModel d) (V : Family.Foliations),
    HasPositivePart volume (D.uncoveredTrace V)

/-- Original mathematical inputs of the P5 conditional theorem. Fields
are ordinary proof arguments, never axioms or global instances. Bôcher and
scalar avoidance now have actual proofs in separate modules. The scalar
fields include the reductions of §7.3, not just external citations. -/
structure P5Inputs : Prop where
  bocher : BocherInput
  cinematicNull : CinematicNullInput
  projectionConstruction : ProjectionConstructionInput
  projectionAvoidance : ProjectionAvoidanceInput

end PlanarNikodym
