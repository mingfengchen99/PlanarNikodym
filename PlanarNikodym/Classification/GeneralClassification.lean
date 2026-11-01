import PlanarNikodym.Cells.DecompositionClassification
import PlanarNikodym.Classification.BallCover
import PlanarNikodym.Core.EmptyFamily

noncomputable section
open Set MeasureTheory Metric
namespace PlanarNikodym

/-- Proposition 1.6 on bounded balls and analytic sublevel domains. The
decomposition retains bounded connected open pieces, auxiliary dimension
bounds, analytic centre-preserving parametrizations, and all four clauses. -/
def Proposition16Statement : Prop :=
  ∀ (d : ℕ) (G : Family 2 d), AnalyticParameterDomain G → G.IsAnalyticAtClosure →
    ∃ D : RankDecomposition G, D.Proposition16Conclusions

structure P6Inputs where
  classification : P5Inputs
  geometry : TameGeometryInput

theorem proposition_1_6_conditional (inputs : P6Inputs) : Proposition16Statement := by
  intro d G hdomain ha
  obtain ⟨D⟩ := lemma_5_7_conditional inputs.geometry d G
    (inputs.geometry.seed d G hdomain ha) hdomain.1 hdomain.2.1 ha.isAnalytic
  exact ⟨D, D.proposition_1_6_of_decomposition inputs.classification ha.isAnalytic⟩

namespace BallParameterCover
variable {d : ℕ} {G : Family 2 d} (C : BallParameterCover G)

theorem analyticAtClosure (ha : G.IsAnalytic) (i : ℕ) :
    (C.toOpenParameterCover.family i).IsAnalyticAtClosure :=
  fun x hx => ha x ⟨hx.1, C.closure_subset i hx.2⟩

theorem analytic_domain (i : ℕ) : AnalyticParameterDomain (C.toOpenParameterCover.family i) :=
  ⟨isOpen_ball, isBounded_ball, Or.inl ⟨C.center i, C.radius i, C.radius_pos i, rfl⟩⟩

def rankDecomposition (geometry : TameGeometryInput) (ha : G.IsAnalytic) (i : ℕ) :
    RankDecomposition (C.toOpenParameterCover.family i) :=
  Classical.choice (lemma_5_7_conditional geometry d (C.toOpenParameterCover.family i)
    (geometry.seed d _ (C.analytic_domain i) (C.analyticAtClosure ha i))
    isOpen_ball isBounded_ball (C.analyticAtClosure ha i).isAnalytic)

/-- All three countable-localization equivalences in §8. The third retains
the no-massive-reuse premise. -/
def LocalizationConclusions : Prop :=
  (G.AdmitsNikodym ↔ ∃ i, (C.toOpenParameterCover.family i).AdmitsNikodym) ∧
  (G.HasMassiveCurveReuse ↔ ∃ i, (C.toOpenParameterCover.family i).HasMassiveCurveReuse) ∧
  (¬ G.HasMassiveCurveReuse →
    (G.LocalReuseNotCovered ↔ ∃ i, (C.toOpenParameterCover.family i).LocalReuseNotCovered))

theorem localization_conditional (inputs : P6Inputs) (ha : G.IsAnalytic) : C.LocalizationConclusions := by
  let O := C.toOpenParameterCover
  let D := C.rankDecomposition inputs.geometry ha
  refine ⟨O.admitsNikodym_iff (fun i hn => (D i).incidence_null_of_noNikodym inputs.classification hn),
    O.hasMassiveCurveReuse_iff (fun i β => (D i).centers_nullMeasurable β), ?_⟩
  intro hm
  apply O.localReuseNotCovered_iff
  intro i hu
  have hmi : ¬ (O.family i).HasMassiveCurveReuse :=
    fun hi => hm ((O.family i).hasMassiveCurveReuse_mono G (O.curves_mono i) hi)
  exact (D i).locallyReusedCovered_of_negative inputs.classification
    (C.analyticAtClosure ha i).isAnalytic hmi
    (fun j hj => hu (((D i).piece j).toAnalyticPiece.localReuseNotCovered_mono hj))

end BallParameterCover

/-- The local-to-global classification. Only analyticity on I×W is needed:
closures of the countable covering balls stay inside W. Empty W is handled
separately, without imposing a spurious nonempty-domain hypothesis. -/
theorem general_classification_of_analytic (inputs : P6Inputs) {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_ball_parameter_cover G ho hne
    let O := C.toOpenParameterCover
    let D := C.rankDecomposition inputs.geometry ha
    obtain ⟨hNik, hMassive, hLocal⟩ := C.localization_conditional inputs ha
    constructor
    · intro hn
      obtain ⟨i, hi⟩ := hNik.mp hn
      rcases ((D i).classification inputs.classification (C.analyticAtClosure ha i).isAnalytic).mp hi with hm | hu
      · exact Or.inl (hMassive.mpr ⟨i, hm⟩)
      · exact Or.inr (G.localReuseNotCovered_restrict_mono (O.domain i) (O.subset i) hu)
    · rintro (hm | hu)
      · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
      · by_cases hm : G.HasMassiveCurveReuse
        · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
        · obtain ⟨i, hi⟩ := (hLocal hm).mp hu
          exact hNik.mpr ⟨i, ((D i).classification inputs.classification
            (C.analyticAtClosure ha i).isAnalytic).mpr (Or.inr hi)⟩
  · exact G.classification_of_empty (Set.not_nonempty_iff_eq_empty.mp hne)

/-- Theorem 1.4 with all P5 and tame-geometry assumptions displayed through
P6Inputs. No new axioms or global instances provide these inputs. -/
theorem theorem_1_4_conditional (inputs : P6Inputs) : Theorem14Statement := by
  intro d G ho ha
  exact general_classification_of_analytic inputs G ho ha.isAnalytic

end PlanarNikodym
