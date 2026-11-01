import PlanarNikodym.Analysis.Maximal.MaximalAssembly
import PlanarNikodym.Classification.GeneralClassification

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- Remaining analytic localization problem: construct actual Fourier,
cutoff, Sobolev, jet-smoothing and reconstruction data near each parameter.
This does not assume a Nikodym or incidence-null conclusion. -/
def CinematicAnalysisInput : Prop :=
  ∀ (d : ℕ) (G : Family 2 d), IsOpen G.W → G.IsAnalytic →
    (∀ t ∈ G.I.carrier, ∀ q ∈ G.W, G.cinematicDet (t, q) ≠ 0) →
    ∀ q ∈ G.W, ∃ U : Set (Parameters 2 d),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧ Nonempty (AnalyticMaximalPackage G U)

/-- P7 discharges the old opaque exclusion interface from explicit
analytic estimates. The analytic input itself is still uninstantiated. -/
theorem cinematicNullInput_of_analysis (h : CinematicAnalysisInput) : CinematicNullInput := by
  intro d G hW ha hn E hE hE0
  rw [G.timeIncidenceCenters_eq ha.isSmooth G.W Subset.rfl E]
  apply G.incidence_null_of_local ?_ E hE hE0
  intro q hq
  obtain ⟨U, hU, hqU, hUW, ⟨D⟩⟩ := h d G hW ha hn q hq
  refine ⟨U, hU, hqU, ?_⟩
  intro F hF hF0
  rw [← G.timeIncidenceCenters_eq ha.isSmooth U hUW F]
  exact D.incidence_null hUW ha.isSmooth F hF hF0

theorem corollary_1_2_conditional (h : CinematicAnalysisInput)
    {d : ℕ} (G : Family 2 d) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hn : ∀ t ∈ G.I.carrier, ∀ q ∈ G.W, G.cinematicDet (t, q) ≠ 0) :
    ¬ G.AdmitsNikodym := by
  apply G.no_nikodym_of_incidence_null
  intro E hE hE0
  rw [← G.timeIncidenceCenters_eq ha.isSmooth G.W Subset.rfl E]
  exact cinematicNullInput_of_analysis h d G hW ha hn E hE hE0

/-- P5 inputs with the former exclusion field replaced by analytic data. -/
structure P7Inputs : Prop where
  bocher : BocherInput
  analysis : CinematicAnalysisInput
  projectionConstruction : ProjectionConstructionInput
  projectionAvoidance : ProjectionAvoidanceInput

theorem P7Inputs.toP5 (h : P7Inputs) : P5Inputs :=
  ⟨h.bocher, cinematicNullInput_of_analysis h.analysis,
    h.projectionConstruction, h.projectionAvoidance⟩

theorem theorem_1_5_from_analysis (h : P7Inputs) : Theorem15Statement :=
  theorem_1_5_conditional h.toP5

theorem theorem_1_4_from_analysis (h : P7Inputs) (geometry : TameGeometryInput) :
    Theorem14Statement :=
  theorem_1_4_conditional ⟨h.toP5, geometry⟩

end PlanarNikodym
