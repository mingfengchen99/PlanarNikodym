import PlanarNikodym.Classification.IntermediateClassification
import PlanarNikodym.Classification.MassiveReuse
import PlanarNikodym.Classification.RankOneClassification

noncomputable section
open Set
namespace PlanarNikodym

/-- Theorem 1.5 under the explicitly listed P5 inputs. All four branches,
including all reuse and foliation clauses, match ConstantRankConclusions.
This interface takes P5Inputs explicitly. Its proved instance is exported by
AnalyticCountableConsequences; the unconditional public theorem is exported
by ProvedAnalyticClassification. -/
theorem theorem_1_5_conditional (inputs : P5Inputs) : Theorem15Statement := by
  intro d G mp mc hWne hW _hbounded ha hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    subst mc
    exact theorem_1_5_case_maximal_gap inputs.bocher inputs.cinematicNull G hW ha hr
  · intro he hz
    subst mp
    subst mc
    exact theorem_1_5_case_rank_one G hWne hW ha hr
  · intro he hm
    subst mc
    exact theorem_1_5_case_positive_intermediate inputs.projectionConstruction
      inputs.projectionAvoidance hm G hWne hW ha hr
  · intro he
    subst mc
    exact theorem_1_5_case_equal G hWne hW ha hr

end PlanarNikodym
