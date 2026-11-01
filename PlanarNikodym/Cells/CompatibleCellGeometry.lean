import PlanarNikodym.Cells.AnalyticCellCover
import PlanarNikodym.Cells.CellRankTransport
import PlanarNikodym.Rank.FiniteRankMinors
import PlanarNikodym.Cells.ReducedGeometry

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- A compatible analytic cell cover. A retained cell is lower dimensional,
or its regular parametrization lands in the specified open regular locus.
This certificate contains no point-rank or curve-rank assertion. -/
structure RegularCellCover {d : ℕ} (G : Family 2 d)
    (tame : (e : ℕ) → Family 2 e → Prop) (D : Set (Parameters 2 d))
    extends AnalyticCellCover G tame where
  lower_or_regular : ∀ i, (piece i).dim < d ∨
    ((piece i).image ⊆ D ∧
      ∀ q ∈ (piece i).family.W, Function.Surjective (fderiv ℝ (piece i).embed q))

/-- Chain rule supplies the rank conclusions of the old one-step input. -/
def RegularCellCover.toRankCellStep {d mp mc : ℕ} {G : Family 2 d}
    {tame : (e : ℕ) → Family 2 e → Prop} {D : Set (Parameters 2 d)}
    (C : RegularCellCover G tame D) (ha : G.IsAnalytic)
    (hr : ∀ p ∈ D, G.pointRank p = mp ∧ G.curveRank p = mc) :
    RankCellStep G tame where
  count := C.count
  piece := C.piece
  exceptional := C.exceptional
  closed_exceptional := C.closed_exceptional
  null_exceptional := C.null_exceptional
  cover := C.cover
  disjoint := C.disjoint
  tame_children := C.tame_children
  ranks_or_lower i := by
    rcases C.lower_or_regular i with hl | ⟨hD, hs⟩
    · exact Or.inl hl
    · refine Or.inr ⟨mp, mc, ?_⟩
      intro q hq
      have he := (C.piece i).ranks_eq_of_surjective ha q hq (hs q hq)
      have hqD := hD (mem_image_of_mem _ hq)
      exact ⟨he.1.trans (hr _ hqD).1, he.2.trans (hr _ hqD).2⟩

/-- The remaining geometric foundation, stated without a rank conclusion.
Only actual finite evaluation minors of the given family's derivatives
are used as compatibility tests. Finiteness of components, preservation of
tameness, and the compatible cell theorem are not proved by this record. -/
structure AnalyticCellInput where
  tame : (d : ℕ) → Family 2 d → Prop
  seed : ∀ (d : ℕ) (G : Family 2 d),
    AnalyticParameterDomain G → G.IsAnalyticAtClosure → tame d G
  components_finite : ∀ (d : ℕ) (G : Family 2 d), tame d G → IsOpen G.W →
    Bornology.IsBounded G.W → G.IsAnalytic → (componentDomains G.W).Finite
  component_tame : ∀ (d : ℕ) (G : Family 2 d), tame d G → IsOpen G.W →
    Bornology.IsBounded G.W → G.IsAnalytic →
    ∀ x ∈ G.W, tame d (G.restrictTo (connectedComponentIn G.W x))
  compatible_cells : ∀ (d : ℕ) (G : Family 2 d), tame d G → IsOpen G.W →
    Bornology.IsBounded G.W → IsConnected G.W → G.IsAnalytic →
    ∀ M : DoubleRankMinor G, G.W ⊆ closure M.regularSet →
      Nonempty (RegularCellCover G tame M.regularSet)

/-- From pure compatible geometry to the old cell/rank step: split into
connected components, construct concrete generic minors, transport ranks
through the regular charts, then flatten. Empty domains are included. -/
def AnalyticCellInput.toTameCell (H : AnalyticCellInput) : TameCellInput where
  tame := H.tame
  seed := H.seed
  step d G ht ho hb ha := by
    classical
    let C := finiteComponentCover G H.tame ho hb ha
      (H.components_finite d G ht ho hb ha) (H.component_tame d G ht ho hb ha)
    have hD (i : Fin C.count) : Nonempty (RankCellStep (C.piece i).family H.tame) := by
      let P := C.piece i
      obtain ⟨M, _, _, _, hMd, hMr⟩ := generic_double_rank_minor P.family
        P.open_domain P.connected_domain P.analytic_family
      obtain ⟨D⟩ := H.compatible_cells P.dim P.family (C.tame_children i)
        P.open_domain P.bounded_domain P.connected_domain P.analytic_family M hMd
      exact ⟨D.toRankCellStep P.analytic_family hMr⟩
    exact ⟨C.flattenRankSteps (fun i => Classical.choice (hD i))⟩

theorem lemma_5_7_from_compatible_cells (H : AnalyticCellInput) (d : ℕ)
    (G : Family 2 d) (ht : H.tame d G) (ho : IsOpen G.W)
    (hb : Bornology.IsBounded G.W) (ha : G.IsAnalytic) :
    Nonempty (RankDecomposition G) :=
  lemma_5_7_after_center_measurability H.toTameCell d G ht ho hb ha

theorem proposition_1_6_from_compatible_cells (h : P8RemainingInputs)
    (H : AnalyticCellInput) : Proposition16Statement :=
  proposition_1_6_after_foundations h H.toTameCell

theorem theorem_1_4_from_compatible_cells (h : P8RemainingInputs)
    (H : AnalyticCellInput) : Theorem14Statement :=
  theorem_1_4_after_foundations h H.toTameCell

end PlanarNikodym
