import PlanarNikodym.Geometry.CenterMeasurability
import PlanarNikodym.Classification.ProvedDependencies

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

def AnalyticPiece.withConstantRanks {d mp mc : ℕ} {G : Family 2 d}
    (P : AnalyticPiece G) (hr : ConstantRanks P.family mp mc) : RankPiece G :=
  { P with
    point_rank := mp
    curve_rank := mc
    ranks := hr
    centers_measurable := P.family.centers_measurable_of_analytic P.open_domain P.analytic_family }

def RankDecomposition.single_proved {d mp mc : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (hb : Bornology.IsBounded G.W) (hc : IsConnected G.W)
    (ha : G.IsAnalytic) (hr : ConstantRanks G mp mc) : RankDecomposition G :=
  RankDecomposition.single G ho hb hc ha hr (G.centers_measurable_of_analytic ho ha)

/-- Only the remaining cell/definability obligations. Borel centre fibres
are now proved from openness and continuity, in every auxiliary dimension. -/
structure TameCellInput where
  tame : (d : ℕ) → Family 2 d → Prop
  seed : ∀ (d : ℕ) (G : Family 2 d), AnalyticParameterDomain G → G.IsAnalyticAtClosure → tame d G
  step : ∀ (d : ℕ) (G : Family 2 d), tame d G → IsOpen G.W → Bornology.IsBounded G.W →
    G.IsAnalytic → Nonempty (RankCellStep G tame)

/-- Add the regularity already guaranteed for seeds and analytic pieces.
This permits the existing P6 recursion to use the proved measurability
theorem without assuming regularity for arbitrary raw `tame` objects. -/
def TameCellInput.toTameGeometry (H : TameCellInput) : TameGeometryInput where
  tame d G := H.tame d G ∧ IsOpen G.W ∧ Bornology.IsBounded G.W ∧ G.IsAnalytic
  seed d G hdom ha := ⟨H.seed d G hdom ha, hdom.1, hdom.2.1, ha.isAnalytic⟩
  centers_measurable _ G ht := G.centers_measurable_of_analytic ht.2.1 ht.2.2.2
  step d G ht ho hb ha := by
    obtain ⟨C⟩ := H.step d G ht.1 ho hb ha
    exact ⟨{
      count := C.count
      piece := C.piece
      exceptional := C.exceptional
      closed_exceptional := C.closed_exceptional
      null_exceptional := C.null_exceptional
      cover := C.cover
      disjoint := C.disjoint
      tame_children := fun i => ⟨C.tame_children i, (C.piece i).open_domain,
        (C.piece i).bounded_domain, (C.piece i).analytic_family⟩
      ranks_or_lower := C.ranks_or_lower }⟩

theorem lemma_5_7_after_center_measurability (H : TameCellInput) (d : ℕ)
    (G : Family 2 d) (ht : H.tame d G) (ho : IsOpen G.W)
    (hb : Bornology.IsBounded G.W) (ha : G.IsAnalytic) : Nonempty (RankDecomposition G) :=
  lemma_5_7_conditional H.toTameGeometry d G ⟨ht, ho, hb, ha⟩ ho hb ha

theorem proposition_1_6_after_foundations (h : P8RemainingInputs) (H : TameCellInput) :
    Proposition16Statement :=
  proposition_1_6_conditional ⟨h.toP7.toP5, H.toTameGeometry⟩

theorem theorem_1_4_after_foundations (h : P8RemainingInputs) (H : TameCellInput) :
    Theorem14Statement := theorem_1_4_after_bocher h H.toTameGeometry

end PlanarNikodym
