import PlanarNikodym.Cells.AnalyticRankCoverExistence
import PlanarNikodym.Classification.ProvedAnalyticClassification

/-! Consequences of the constructed countable analytic rank cover.
This module proves the forward implication of the general classification
using the constructed rank cover. The complete public results are exported
by GeneralAnalyticClassification and PaperProposition16. -/

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem p5_inputs_proved : P5Inputs :=
  p5Inputs_of_smooth_analysis cinematic_smooth_analysis_input
    projection_construction_input projection_avoidance_input

/-- The forward direction of general analytic classification, using the
actual countable rank cover and the proved constant-rank classification. -/
theorem Family.general_classification_forward_proved {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    G.AdmitsNikodym → G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  obtain ⟨D⟩ := G.exists_analyticRankCover ho ha
  exact D.classification_forward p5_inputs_proved

/-- The forward half with exactly the geometric assumptions appearing
in the original `Theorem14Statement`, and no cell Input argument. -/
theorem theorem_1_4_forward_proved :
    ∀ (d : ℕ) (G : Family 2 d), IsOpen G.W → G.IsAnalyticAtClosure →
      G.AdmitsNikodym → G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  intro d G ho ha
  exact G.general_classification_forward_proved ho ha.isAnalytic

/-- Absence of Nikodym sets implies zero outer measure of the incidence
centres for every Borel planar null set, in every open analytic family. -/
theorem Family.incidence_null_of_noNikodym_proved {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (hn : ¬ G.AdmitsNikodym) :
    ∀ E, MeasurableSet E → volume E = 0 →
      volume (G.incidenceCenters G.W E) = 0 := by
  obtain ⟨D⟩ := G.exists_analyticRankCover ho ha
  exact D.incidence_null_of_noNikodym p5_inputs_proved hn

/-- At least one of the actual countably many constant-rank subfamilies
already witnesses Nikodym existence, whenever the original family does. -/
theorem Family.exists_rankPiece_of_admitsNikodym {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (hn : G.AdmitsNikodym) :
    ∃ P : RankPiece G, P.family.AdmitsNikodym := by
  obtain ⟨D⟩ := G.exists_analyticRankCover ho ha
  obtain ⟨P, _, hp⟩ := (D.admitsNikodym_iff p5_inputs_proved).mp hn
  exact ⟨P, hp⟩

/-- The two positive-volume properties localize simultaneously to one
constructed countable rank cover; the local H¹-reuse equivalence is not
part of this statement. -/
theorem Family.exists_rankCover_localization {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    ∃ D : AnalyticRankCover G,
      (G.AdmitsNikodym ↔ ∃ P ∈ D.pieces, P.family.AdmitsNikodym) ∧
      (G.HasMassiveCurveReuse ↔ ∃ P ∈ D.pieces, P.family.HasMassiveCurveReuse) := by
  obtain ⟨D⟩ := G.exists_analyticRankCover ho ha
  exact ⟨D, D.admitsNikodym_iff p5_inputs_proved, D.hasMassiveCurveReuse_iff⟩

end PlanarNikodym
