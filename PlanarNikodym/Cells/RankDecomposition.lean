import PlanarNikodym.Cells.AnalyticPieces

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- The geometric certificate required from bounded analytic rank
stratification. It has no Nikodym or foliation conclusions. -/
structure RankDecomposition {d : ℕ} (G : Family 2 d) where
  count : ℕ
  piece : Fin count → RankPiece G
  exceptional : Set (Base 2)
  closed_exceptional : IsClosed exceptional
  null_exceptional : volume exceptional = 0
  cover : ∀ p ∈ G.W, p.1 ∈ exceptional ∨ ∃ i, p ∈ (piece i).toAnalyticPiece.image
  disjoint : Pairwise (fun i j => Disjoint (piece i).toAnalyticPiece.image (piece j).toAnalyticPiece.image)

def RankDecomposition.remainder {d : ℕ} {G : Family 2 d} (D : RankDecomposition G) :
    Set (Parameters 2 d) := G.W \ ⋃ i, (D.piece i).toAnalyticPiece.image

theorem RankDecomposition.partition {d : ℕ} {G : Family 2 d} (D : RankDecomposition G) :
    G.W = (⋃ i, (D.piece i).toAnalyticPiece.image) ∪ D.remainder := by
  ext p
  constructor
  · intro hp
    by_cases hi : p ∈ ⋃ i, (D.piece i).toAnalyticPiece.image
    · exact Or.inl hi
    · exact Or.inr ⟨hp, hi⟩
  · rintro (hi | hi)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hi
      exact (D.piece i).toAnalyticPiece.image_subset hi
    · exact hi.1

theorem RankDecomposition.remainder_disjoint {d : ℕ} {G : Family 2 d} (D : RankDecomposition G)
    (i : Fin D.count) : Disjoint (D.piece i).toAnalyticPiece.image D.remainder := by
  apply disjoint_left.mpr
  intro p hp hr
  exact hr.2 (mem_iUnion.mpr ⟨i, hp⟩)

theorem RankDecomposition.remainder_centers_closure_null {d : ℕ} {G : Family 2 d}
    (D : RankDecomposition G) : volume (closure (Prod.fst '' D.remainder)) = 0 := by
  apply measure_mono_null (closure_minimal ?_ D.closed_exceptional) D.null_exceptional
  rintro z ⟨p, hp, rfl⟩
  rcases D.cover p hp.1 with hb | ⟨i, hi⟩
  · exact hb
  · exact (hp.2 (mem_iUnion.mpr ⟨i, hi⟩)).elim

def AnalyticPiece.refl {d : ℕ} (G : Family 2 d) (ho : IsOpen G.W)
    (hb : Bornology.IsBounded G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic) : AnalyticPiece G where
  dim := d
  dim_le := le_rfl
  family := G
  interval_eq := rfl
  open_domain := ho
  bounded_domain := hb
  connected_domain := hc
  analytic_family := ha
  embed := id
  inverse := id
  analytic_embed := fun _ _ => analyticAt_id
  continuous_inverse := continuousOn_id
  left_inv := fun _ _ => rfl
  keep_center := fun _ _ => rfl
  maps_to := fun _ hp => hp
  identity := fun _ _ _ _ => rfl

def RankDecomposition.single {d mp mc : ℕ} (G : Family 2 d) (ho : IsOpen G.W)
    (hb : Bornology.IsBounded G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G mp mc) (hm : ∀ β, MeasurableSet (G.centersOf β)) : RankDecomposition G where
  count := 1
  piece := fun _ => { AnalyticPiece.refl G ho hb hc ha with
    point_rank := mp, curve_rank := mc, ranks := hr, centers_measurable := hm }
  exceptional := ∅
  closed_exceptional := isClosed_empty
  null_exceptional := measure_empty
  cover := fun p hp => Or.inr ⟨0, p, hp, rfl⟩
  disjoint := fun i j hn => (hn (Subsingleton.elim i j)).elim

/-- One cell/rank reduction step. Full-dimensional children have constant
ranks; every other child has strictly fewer auxiliary variables. The closed
null centre exception includes closures of exceptional projections. -/
structure RankCellStep {d : ℕ} (G : Family 2 d)
    (tame : (e : ℕ) → Family 2 e → Prop) where
  count : ℕ
  piece : Fin count → AnalyticPiece G
  exceptional : Set (Base 2)
  closed_exceptional : IsClosed exceptional
  null_exceptional : volume exceptional = 0
  cover : ∀ p ∈ G.W, p.1 ∈ exceptional ∨ ∃ i, p ∈ (piece i).image
  disjoint : Pairwise (fun i j => Disjoint (piece i).image (piece j).image)
  tame_children : ∀ i, tame (piece i).dim (piece i).family
  ranks_or_lower : ∀ i, (piece i).dim < d ∨
    ∃ mp mc, ConstantRanks (piece i).family mp mc

/-- Flatten a finite family of recursively decomposed analytic cells. This
is the dimension-induction step behind the bounded form of Lemma 5.7. -/
def RankCellStep.flatten {d : ℕ} {G : Family 2 d}
    {tame : (e : ℕ) → Family 2 e → Prop} (C : RankCellStep G tame)
    (D : (i : Fin C.count) → RankDecomposition (C.piece i).family) : RankDecomposition G := by
  classical
  let ι := (i : Fin C.count) × Fin (D i).count
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let P : ι → RankPiece G := fun i => RankPiece.comp (C.piece i.1) ((D i.1).piece i.2)
  have hsub (i : ι) : (P i).toAnalyticPiece.image ⊆ (C.piece i.1).image := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨((D i.1).piece i.2).embed p, ((D i.1).piece i.2).maps_to p hp, rfl⟩
  have hdisj : Pairwise (fun i j : ι => Disjoint (P i).toAnalyticPiece.image (P j).toAnalyticPiece.image) := by
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
  refine ⟨Fintype.card ι, fun i => P (e i), C.exceptional ∪ ⋃ i, (D i).exceptional,
    C.closed_exceptional.union (isClosed_iUnion_of_finite (fun i => (D i).closed_exceptional)),
    measure_union_null C.null_exceptional (measure_iUnion_null (fun i => (D i).null_exceptional)),
    ?_, fun i j h => hdisj (fun he => h (e.injective he))⟩
  intro p hp
  rcases C.cover p hp with hb | ⟨i, q, hq, hqp⟩
  · exact Or.inl (Or.inl hb)
  · rcases (D i).cover q hq with hb | ⟨j, r, hr, hrq⟩
    · apply Or.inl
      apply Or.inr
      have hz : p.1 = q.1 := (congrArg Prod.fst hqp).symm.trans ((C.piece i).keep_center q hq)
      rw [hz]
      exact mem_iUnion.mpr ⟨i, hb⟩
    · apply Or.inr
      refine ⟨e.symm ⟨i, j⟩, ?_⟩
      rw [e.apply_symm_apply]
      refine ⟨r, hr, ?_⟩
      change (C.piece i).embed (((D i).piece j).embed r) = p
      rw [hrq, hqp]

/-- Domains used in the stated form of Proposition 1.6. Balls use the fixed
norm on Parameters; the analytic sublevel alternative is also retained. -/
def AnalyticParameterDomain {d : ℕ} (G : Family 2 d) : Prop :=
  IsOpen G.W ∧ Bornology.IsBounded G.W ∧
    ((∃ c r, 0 < r ∧ G.W = Metric.ball c r) ∨
      ∃ f : Parameters 2 d → ℝ, AnalyticOnNhd ℝ f (closure G.W) ∧ G.W = {p | f p < 0})

/-- Legacy tame-geometry interface. P8 proves Borel centre fibres from
openness and continuity, and ReducedGeometry supplies this field through
`TameCellInput.toTameGeometry`. The tame predicate, seeds and actual finite
cell/rank step remain uninstantiated. No classification is assumed here. -/
structure TameGeometryInput where
  tame : (d : ℕ) → Family 2 d → Prop
  seed : ∀ (d : ℕ) (G : Family 2 d), AnalyticParameterDomain G → G.IsAnalyticAtClosure → tame d G
  centers_measurable : ∀ (d : ℕ) (G : Family 2 d), tame d G →
    ∀ β : Set Plane, MeasurableSet (G.centersOf β)
  step : ∀ (d : ℕ) (G : Family 2 d), tame d G → IsOpen G.W → Bornology.IsBounded G.W →
    G.IsAnalytic → Nonempty (RankCellStep G tame)

/-- Bounded rank-stratification (the part of Lemma 5.7 used in P6), proved
by strong induction on auxiliary dimension from the one-step input. -/
theorem lemma_5_7_conditional (geometry : TameGeometryInput) (d : ℕ) (G : Family 2 d)
    (ht : geometry.tame d G) (ho : IsOpen G.W) (hb : Bornology.IsBounded G.W)
    (ha : G.IsAnalytic) : Nonempty (RankDecomposition G) := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain ⟨C⟩ := geometry.step d G ht ho hb ha
    have hD (i : Fin C.count) : Nonempty (RankDecomposition (C.piece i).family) := by
      rcases C.ranks_or_lower i with hl | ⟨mp, mc, hr⟩
      · exact ih (C.piece i).dim hl (C.piece i).family (C.tame_children i)
          (C.piece i).open_domain (C.piece i).bounded_domain (C.piece i).analytic_family
      · exact ⟨RankDecomposition.single (C.piece i).family (C.piece i).open_domain
          (C.piece i).bounded_domain (C.piece i).connected_domain (C.piece i).analytic_family hr
          (geometry.centers_measurable _ _ (C.tame_children i))⟩
    exact ⟨C.flatten (fun i => Classical.choice (hD i))⟩

end PlanarNikodym
