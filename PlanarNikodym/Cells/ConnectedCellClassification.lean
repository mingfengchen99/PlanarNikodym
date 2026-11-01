import PlanarNikodym.Cells.CompatibleCellGeometry

noncomputable section
open Set MeasureTheory Metric
namespace PlanarNikodym

/-- For the general classification, only ball seeds and compatible cells
on connected domains are needed. Finiteness of all connected components
is not an assumption of this smaller interface. Cell existence remains
an explicit unproved input. -/
structure ConnectedCellInput where
  tame : (d : ℕ) → Family 2 d → Prop
  seed_ball : ∀ (d : ℕ) (G : Family 2 d) (c : Parameters 2 d) (r : ℝ),
    0 < r → G.W = ball c r → G.IsAnalyticAtClosure → tame d G
  compatible_cells : ∀ (d : ℕ) (G : Family 2 d), tame d G → IsOpen G.W →
    Bornology.IsBounded G.W → IsConnected G.W → G.IsAnalytic →
    ∀ M : DoubleRankMinor G, G.W ⊆ closure M.regularSet →
      Nonempty (RegularCellCover G tame M.regularSet)

def AnalyticCellInput.toConnected (H : AnalyticCellInput) : ConnectedCellInput where
  tame := H.tame
  seed_ball d G c r hr he ha := H.seed d G
    ⟨he ▸ isOpen_ball, he ▸ isBounded_ball, Or.inl ⟨c, r, hr, he⟩⟩ ha
  compatible_cells := H.compatible_cells

/-- The connected case of the bounded rank decomposition, by strong
induction on auxiliary dimension. All children are connected by their
analytic-piece certificates. -/
theorem lemma_5_7_connected_cells (H : ConnectedCellInput) (d : ℕ)
    (G : Family 2 d) (ht : H.tame d G) (ho : IsOpen G.W)
    (hb : Bornology.IsBounded G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic) :
    Nonempty (RankDecomposition G) := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain ⟨M, _, _, _, hMd, hMr⟩ := generic_double_rank_minor G ho hc ha
    obtain ⟨cells⟩ := H.compatible_cells d G ht ho hb hc ha M hMd
    let C := cells.toRankCellStep ha hMr
    have hD (i : Fin C.count) : Nonempty (RankDecomposition (C.piece i).family) := by
      rcases C.ranks_or_lower i with hl | ⟨mp, mc, hr⟩
      · exact ih (C.piece i).dim hl (C.piece i).family (C.tame_children i)
          (C.piece i).open_domain (C.piece i).bounded_domain (C.piece i).connected_domain
          (C.piece i).analytic_family
      · exact ⟨RankDecomposition.single_proved (C.piece i).family
          (C.piece i).open_domain (C.piece i).bounded_domain (C.piece i).connected_domain
          (C.piece i).analytic_family hr⟩
    exact ⟨C.flatten (fun i => Classical.choice (hD i))⟩

/-- The three localization equivalences require actual local rank
decompositions, independently of how those decompositions were obtained. -/
theorem BallParameterCover.localization_of_decompositions {d : ℕ} {G : Family 2 d}
    (C : BallParameterCover G) (inputs : P5Inputs) (ha : G.IsAnalytic)
    (D : ∀ i, RankDecomposition (C.toOpenParameterCover.family i)) :
    C.LocalizationConclusions := by
  let O := C.toOpenParameterCover
  refine ⟨O.admitsNikodym_iff (fun i hn => (D i).incidence_null_of_noNikodym inputs hn),
    O.hasMassiveCurveReuse_iff (fun i β => (D i).centers_nullMeasurable β), ?_⟩
  intro hm
  apply O.localReuseNotCovered_iff
  intro i hu
  have hmi : ¬ (O.family i).HasMassiveCurveReuse :=
    fun hi => hm ((O.family i).hasMassiveCurveReuse_mono G (O.curves_mono i) hi)
  exact (D i).locallyReusedCovered_of_negative inputs
    (C.analyticAtClosure ha i).isAnalytic hmi
    (fun j hj => hu (((D i).piece j).toAnalyticPiece.localReuseNotCovered_mono hj))

def BallParameterCover.connectedRankDecomposition {d : ℕ} {G : Family 2 d}
    (C : BallParameterCover G) (H : ConnectedCellInput) (ha : G.IsAnalytic) (i : ℕ) :
    RankDecomposition (C.toOpenParameterCover.family i) :=
  Classical.choice (lemma_5_7_connected_cells H d (C.toOpenParameterCover.family i)
    (H.seed_ball d _ (C.center i) (C.radius i) (C.radius_pos i) rfl
      (C.analyticAtClosure ha i)) isOpen_ball isBounded_ball
    ((convex_ball (C.center i) (C.radius i)).isConnected
      ⟨C.center i, mem_ball_self (C.radius_pos i)⟩) (C.analyticAtClosure ha i).isAnalytic)

/-- Theorem 1.4's local-to-global argument needs no finite-component
theorem. The remaining inputs are classification analysis/projections and
the compatible connected-cell foundation. -/
theorem general_classification_from_connected_cells (h : P8RemainingInputs)
    (H : ConnectedCellInput) {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_ball_parameter_cover G ho hne
    let O := C.toOpenParameterCover
    let D := C.connectedRankDecomposition H ha
    let inputs := h.toP7.toP5
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

theorem theorem_1_4_from_connected_cells (h : P8RemainingInputs) (H : ConnectedCellInput) :
    Theorem14Statement := by
  intro d G ho ha
  exact general_classification_from_connected_cells h H G ho ha.isAnalytic

end PlanarNikodym
