import PlanarNikodym.Analysis.Maximal.SmoothMaximalAssembly
import PlanarNikodym.Analysis.Sobolev.BandSobolevRegularity
import PlanarNikodym.Cells.ConnectedCellClassification

/-! Classification through the proved smooth-test reconstruction route.
The remaining smoothing and geometric inputs are displayed explicitly. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff NNReal
namespace PlanarNikodym

/-- In one auxiliary dimension only jet smoothing remains an analytic
estimate: the Sobolev field is supplied by the proved regularity theorem. -/
def smoothMaximalPackage_aux_one (G : Family 2 1) (U : Set (Parameters 2 1))
    (χ : Cutoff 1) (L : FrequencyCutoff) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ,
      ContDiffAt ℝ 1 (fun x : ℝ × Parameters 2 1 => G.γ x.1 x.2) x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ t ∈ G.I.carrier, ∀ q ∈ U, 1 ≤ χ (t, q))
    (p : ℝ≥0) (hp : smoothingThreshold 1 ≤ p)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / (p : ℝ))
    (hS : JetSmoothingInput G χ L p 1 ε) : SmoothMaximalPackage G U := by
  have hp1 : 1 ≤ p := (by norm_num [smoothingThreshold] : (1 : ℝ≥0) ≤ smoothingThreshold 1).trans hp
  let δ : ℝ := (1 / (p : ℝ) - ε) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  exact {
    frequency := L
    cutoff := χ
    cutoff_smooth := hχ
    cutoff_compact := hc
    gamma_regular_at_support := hγ
    cutoff_nonnegative := hχ0
    cutoff_one := hχ1
    p := p
    p_ge_one := hp1
    p_ge_threshold := hp
    jetOrder := 1
    jetOrder_gt := by simpa only [Nat.cast_one] using smoothingThreshold_sobolev_order_one 1 p hp
    smoothingLoss := ε
    sobolevLoss := δ
    smoothingLoss_pos := hε0
    sobolevLoss_pos := hδ
    loss_lt := by dsimp [δ]; linarith
    smoothing := hS
    sobolev := G.bandSobolevInput_aux_one χ (hχ.of_le (by simp)) hc hγ L p hp1 δ hδ.le }

/-- This is the remaining local analytic construction problem. Low-frequency,
reconstruction and maximal-function measurability are not proof fields. -/
def CinematicSmoothAnalysisInput : Prop :=
  ∀ (d : ℕ) (G : Family 2 d), IsOpen G.W → G.IsAnalytic →
    (∀ t ∈ G.I.carrier, ∀ q ∈ G.W, G.cinematicDet (t, q) ≠ 0) →
    ∀ q ∈ G.W, ∃ U : Set (Parameters 2 d),
      IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧ Nonempty (SmoothMaximalPackage G U)

theorem cinematicNullInput_of_smooth_analysis (h : CinematicSmoothAnalysisInput) :
    CinematicNullInput := by
  intro d G hW ha hn E hE hE0
  rw [G.timeIncidenceCenters_eq ha.isSmooth G.W Subset.rfl E]
  apply G.incidence_null_of_local ?_ E hE hE0
  intro q hq
  obtain ⟨U, hU, hqU, hUW, ⟨D⟩⟩ := h d G hW ha hn q hq
  refine ⟨U, hU, hqU, ?_⟩
  intro F hF hF0
  rw [← G.timeIncidenceCenters_eq ha.isSmooth U hUW F]
  exact (D.open_maximal_estimate hU hUW ha.isSmooth).incidence_null hUW ha.isSmooth F hF hF0

theorem p5Inputs_of_smooth_analysis (h : CinematicSmoothAnalysisInput)
    (hP : ProjectionConstructionInput) (hV : ProjectionAvoidanceInput) : P5Inputs :=
  ⟨bocher_input, cinematicNullInput_of_smooth_analysis h, hP, hV⟩

theorem theorem_1_5_from_smooth_analysis (h : CinematicSmoothAnalysisInput)
    (hP : ProjectionConstructionInput) (hV : ProjectionAvoidanceInput) : Theorem15Statement :=
  theorem_1_5_conditional (p5Inputs_of_smooth_analysis h hP hV)

/-- The connected-cell local-to-global argument works for actual P5 inputs,
independently of which analytic route supplies cinematic exclusion. -/
theorem general_classification_connected_of_p5 (inputs : P5Inputs)
    (H : ConnectedCellInput) {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_ball_parameter_cover G ho hne
    let O := C.toOpenParameterCover
    let D := C.connectedRankDecomposition H ha
    obtain ⟨hNik, hMassive, hLocal⟩ := C.localization_of_decompositions inputs ha D
    constructor
    · intro hn
      obtain ⟨i, hi⟩ := hNik.mp hn
      rcases ((D i).classification inputs (C.analyticAtClosure ha i).isAnalytic).mp hi with hm | hu
      · exact Or.inl (hMassive.mpr ⟨i, hm⟩)
      · exact Or.inr (G.localReuseNotCovered_restrict_mono (O.domain i) (O.subset i) hu)
    · rintro (hm | hu)
      · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
      · by_cases hm : G.HasMassiveCurveReuse
        · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
        · obtain ⟨i, hi⟩ := (hLocal hm).mp hu
          exact hNik.mpr ⟨i, ((D i).classification inputs
            (C.analyticAtClosure ha i).isAnalytic).mpr (Or.inr hi)⟩
  · exact G.classification_of_empty (Set.not_nonempty_iff_eq_empty.mp hne)

theorem theorem_1_4_from_smooth_analysis (h : CinematicSmoothAnalysisInput)
    (hP : ProjectionConstructionInput) (hV : ProjectionAvoidanceInput)
    (H : ConnectedCellInput) : Theorem14Statement := by
  intro d G ho ha
  exact general_classification_connected_of_p5 (p5Inputs_of_smooth_analysis h hP hV) H G ho ha.isAnalytic

theorem proposition_1_6_from_smooth_analysis (h : CinematicSmoothAnalysisInput)
    (hP : ProjectionConstructionInput) (hV : ProjectionAvoidanceInput)
    (H : AnalyticCellInput) : Proposition16Statement :=
  proposition_1_6_conditional
    ⟨p5Inputs_of_smooth_analysis h hP hV, H.toTameCell.toTameGeometry⟩

end PlanarNikodym
