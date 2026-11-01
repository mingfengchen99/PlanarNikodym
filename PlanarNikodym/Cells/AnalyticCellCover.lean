import PlanarNikodym.Cells.RankDecomposition
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- Finite analytic geometry with no rank conclusions. The exceptional
centres include their closure and have zero outer measure. -/
structure AnalyticCellCover {d : ℕ} (G : Family 2 d)
    (tame : (e : ℕ) → Family 2 e → Prop) where
  count : ℕ
  piece : Fin count → AnalyticPiece G
  exceptional : Set (Base 2)
  closed_exceptional : IsClosed exceptional
  null_exceptional : volume exceptional = 0
  cover : ∀ p ∈ G.W, p.1 ∈ exceptional ∨ ∃ i, p ∈ (piece i).image
  disjoint : Pairwise (fun i j => Disjoint (piece i).image (piece j).image)
  tame_children : ∀ i, tame (piece i).dim (piece i).family

/-- Flatten finite analytic covers followed by rank steps. All rank
information comes from the inner steps, not from the outer cover. -/
def AnalyticCellCover.flattenRankSteps {d : ℕ} {G : Family 2 d}
    {tame : (e : ℕ) → Family 2 e → Prop} (C : AnalyticCellCover G tame)
    (D : (i : Fin C.count) → RankCellStep (C.piece i).family tame) :
    RankCellStep G tame := by
  classical
  let ι := (i : Fin C.count) × Fin (D i).count
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P : ι → AnalyticPiece G := fun i => (C.piece i.1).comp ((D i.1).piece i.2)
  have hsub (i : ι) : (P i).image ⊆ (C.piece i.1).image := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨((D i.1).piece i.2).embed p, ((D i.1).piece i.2).maps_to p hp, rfl⟩
  have hdisj : Pairwise (fun i j : ι => Disjoint (P i).image (P j).image) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hne
    by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := fun he => hne (by subst l; rfl)
      apply disjoint_left.mpr
      rintro z ⟨p, hp, hpz⟩ ⟨q, hq, hqz⟩
      have he : ((D i).piece j).embed p = ((D i).piece l).embed q :=
        (C.piece i).embed_injOn (((D i).piece j).maps_to p hp)
          (((D i).piece l).maps_to q hq) (hpz.trans hqz.symm)
      exact disjoint_left.mp ((D i).disjoint hjl)
        (mem_image_of_mem _ hp) (he ▸ mem_image_of_mem ((D i).piece l).embed hq)
    · exact (C.disjoint hik).mono (hsub ⟨i, j⟩) (hsub ⟨k, l⟩)
  refine {
    count := Fintype.card ι
    piece := fun i => P (e i)
    exceptional := C.exceptional ∪ ⋃ i, (D i).exceptional
    closed_exceptional := C.closed_exceptional.union
      (isClosed_iUnion_of_finite (fun i => (D i).closed_exceptional))
    null_exceptional := measure_union_null C.null_exceptional
      (measure_iUnion_null (fun i => (D i).null_exceptional))
    cover := ?_
    disjoint := fun i j h => hdisj (fun he => h (e.injective he))
    tame_children := fun i => (D (e i).1).tame_children (e i).2
    ranks_or_lower := ?_ }
  · intro p hp
    rcases C.cover p hp with hb | ⟨i, q, hq, hqp⟩
    · exact Or.inl (Or.inl hb)
    · rcases (D i).cover q hq with hb | ⟨j, r, hr, hrq⟩
      · apply Or.inl
        apply Or.inr
        have hz : p.1 = q.1 :=
          (congrArg Prod.fst hqp).symm.trans ((C.piece i).keep_center q hq)
        rw [hz]
        exact mem_iUnion.mpr ⟨i, hb⟩
      · apply Or.inr
        refine ⟨e.symm ⟨i, j⟩, ?_⟩
        rw [e.apply_symm_apply]
        refine ⟨r, hr, ?_⟩
        change (C.piece i).embed (((D i).piece j).embed r) = p
        rw [hrq, hqp]
  · intro i
    rcases (D (e i).1).ranks_or_lower (e i).2 with hl | hr
    · exact Or.inl (hl.trans_le (C.piece (e i).1).dim_le)
    · exact Or.inr hr

/-- Actual nonempty connected components, represented as subsets of the
ambient parameter space. Their finiteness is a separate tame hypothesis. -/
def componentDomains {E : Type*} [TopologicalSpace E] (W : Set E) : Set (Set E) :=
  {U | ∃ x ∈ W, U = connectedComponentIn W x}

/-- Topology supplies all component parametrizations, disjointness and
coverage once finiteness and closure of the tame predicate are supplied.
This handles empty domains without invoking a generic-rank theorem. -/
def finiteComponentCover {d : ℕ} (G : Family 2 d)
    (tame : (e : ℕ) → Family 2 e → Prop)
    (ho : IsOpen G.W) (hb : Bornology.IsBounded G.W) (ha : G.IsAnalytic)
    (hf : (componentDomains G.W).Finite)
    (ht : ∀ x ∈ G.W, tame d (G.restrictTo (connectedComponentIn G.W x))) :
    AnalyticCellCover G tame := by
  classical
  let ι := componentDomains G.W
  letI : Fintype ι := hf.fintype
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hsub (U : ι) : U.val ⊆ G.W := by
    obtain ⟨x, _, hx⟩ := U.property
    rw [hx]
    exact connectedComponentIn_subset G.W x
  have hopen (U : ι) : IsOpen U.val := by
    obtain ⟨x, _, hx⟩ := U.property
    rw [hx]
    exact ho.connectedComponentIn
  have hconn (U : ι) : IsConnected U.val := by
    obtain ⟨x, hxW, hx⟩ := U.property
    rw [hx]
    exact isConnected_connectedComponentIn_iff.mpr hxW
  let P (U : ι) : AnalyticPiece G := AnalyticPiece.restrict G U.val (hopen U)
    (hb.subset (hsub U)) (hconn U) (fun p hp => ha p ⟨hp.1, hsub U hp.2⟩) (hsub U)
  refine {
    count := Fintype.card ι
    piece := fun i => P (e i)
    exceptional := ∅
    closed_exceptional := isClosed_empty
    null_exceptional := measure_empty
    cover := ?_
    disjoint := ?_
    tame_children := ?_ }
  · intro p hp
    let U : ι := ⟨connectedComponentIn G.W p, p, hp, rfl⟩
    refine Or.inr ⟨e.symm U, p, ?_, rfl⟩
    change p ∈ (e (e.symm U)).val
    rw [e.apply_symm_apply]
    exact mem_connectedComponentIn hp
  · intro i j hij
    apply disjoint_left.mpr
    rintro p ⟨q, hq, hqp⟩ ⟨r, hr, hrp⟩
    change q = p at hqp
    change r = p at hrp
    subst q
    subst r
    change p ∈ (e i).val at hq
    change p ∈ (e j).val at hr
    obtain ⟨x, _, hx⟩ := (e i).property
    obtain ⟨y, _, hy⟩ := (e j).property
    have hsame : (e i).val = (e j).val := by
      rw [hx, hy]
      exact (connectedComponentIn_eq (hx ▸ hq)).trans
        (connectedComponentIn_eq (hy ▸ hr)).symm
    exact hij (e.injective (Subtype.ext hsame))
  · intro i
    obtain ⟨x, hxW, hx⟩ := (e i).property
    change tame d (G.restrictTo (e i).val)
    rw [hx]
    exact ht x hxW

end PlanarNikodym
