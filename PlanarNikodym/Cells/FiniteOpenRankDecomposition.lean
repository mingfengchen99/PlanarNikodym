import PlanarNikodym.Cells.ReducedGeometry
import PlanarNikodym.Tame.FamilySemantics
import PlanarNikodym.Geometry.SemianalyticComponentUnions

/-! Finite disjoint open semianalytic rank regions give the actual legacy
RankDecomposition. Connected components, open bounded source domains,
center-preserving maps and disjointness are constructed explicitly. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.exists_rankDecomposition_of_finite_open_regions
    {d N : ℕ} (G : Family 2 d) (ha : G.IsAnalytic)
    (C : Fin N → Set (Fin (d + 2) → ℝ))
    (hCo : ∀ i, IsOpen (C i)) (hCs : ∀ i, LocallySemianalytic (C i))
    (hCb : ∀ i, Bornology.IsBounded (C i))
    (hCW : ∀ i, (parameterFrame d) '' C i ⊆ G.W)
    (mp mc : Fin N → ℕ)
    (hr : ∀ i, ∀ x ∈ C i,
      G.pointRank (parameterFrame d x) = mp i ∧
      G.curveRank (parameterFrame d x) = mc i)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (E : Set (Base 2)) (hEc : IsClosed E) (hEn : volume E = 0)
    (hcover : ∀ p ∈ G.W, p.1 ∈ E ∨ ∃ i, (parameterFrame d).symm p ∈ C i) :
    Nonempty (RankDecomposition G) := by
  classical
  let e := parameterFrame d
  letI (i : Fin N) : Fintype (componentDomains (C i)) :=
    ((hCs i).components_finite_of_bounded (hCb i)).fintype
  let J := (i : Fin N) × componentDomains (C i)
  have hsub (j : J) : j.2.val ⊆ C j.1 := by
    obtain ⟨x, _, hj⟩ := j.2.property
    rw [hj]
    exact connectedComponentIn_subset _ _
  have hopen (j : J) : IsOpen j.2.val := by
    obtain ⟨x, _, hj⟩ := j.2.property
    rw [hj]
    exact (hCo j.1).connectedComponentIn
  have hconn (j : J) : IsConnected j.2.val := by
    obtain ⟨x, hx, hj⟩ := j.2.property
    rw [hj]
    exact isConnected_connectedComponentIn_iff.mpr hx
  let U (j : J) := e '' j.2.val
  have hUW (j : J) : U j ⊆ G.W := (image_mono (hsub j)).trans (hCW j.1)
  let R (j : J) : AnalyticPiece G := AnalyticPiece.restrict G (U j)
    (e.toHomeomorph.isOpenMap _ (hopen j))
    (e.lipschitz.isBounded_image ((hCb j.1).subset (hsub j)))
    ((hconn j).image e e.continuous.continuousOn) (ha.restrictTo (hUW j)) (hUW j)
  have hRrank (j : J) : ConstantRanks (R j).family (mp j.1) (mc j.1) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hr j.1 x (hsub j hx)
  let P (j : J) : RankPiece G := (R j).withConstantRanks (hRrank j)
  let f : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨{
    count := Fintype.card J
    piece := fun i => P (f i)
    exceptional := E
    closed_exceptional := hEc
    null_exceptional := hEn
    cover := ?_
    disjoint := ?_ }⟩
  · intro p hp
    rcases hcover p hp with he | ⟨i, hi⟩
    · exact Or.inl he
    let V : componentDomains (C i) := ⟨connectedComponentIn (C i) (e.symm p),
      e.symm p, hi, rfl⟩
    refine Or.inr ⟨f.symm ⟨i, V⟩, p, ?_, rfl⟩
    change p ∈ U (f (f.symm ⟨i, V⟩))
    rw [f.apply_symm_apply]
    exact ⟨e.symm p, mem_connectedComponentIn hi, e.apply_symm_apply p⟩
  · intro a b hab
    apply disjoint_left.mpr
    rintro p ⟨q, hq, hqp⟩ ⟨r, hrr, hrp⟩
    change q = p at hqp
    change r = p at hrp
    subst q
    subst r
    change p ∈ U (f a) at hq
    change p ∈ U (f b) at hrr
    obtain ⟨x, hx, hxp⟩ := hq
    obtain ⟨y, hy, hyp⟩ := hrr
    have hxy : x = y := e.injective (hxp.trans hyp.symm)
    subst y
    have hij : (f a).1 = (f b).1 := by
      by_contra hn
      exact disjoint_left.mp (hdisj hn) (hsub (f a) hx) (hsub (f b) hy)
    have hjeq : f a = f b := by
      have haux : ∀ (i j : Fin N) (V : componentDomains (C i))
          (W : componentDomains (C j)), i = j → x ∈ V.val → x ∈ W.val →
          (Sigma.mk i V : J) = Sigma.mk j W := by
        intro i j V W hij hx hy
        subst j
        have hVW : V = W := by
          apply Subtype.ext
          obtain ⟨v, _, hV⟩ := V.property
          obtain ⟨w, _, hW⟩ := W.property
          exact hV.trans ((connectedComponentIn_eq (hV ▸ hx)).trans
            ((connectedComponentIn_eq (hW ▸ hy)).symm.trans hW.symm))
        exact congrArg (Sigma.mk i) hVW
      exact haux (f a).1 (f b).1 (f a).2 (f b).2 hij hx hy
    exact hab (f.injective hjeq)

end PlanarNikodym
