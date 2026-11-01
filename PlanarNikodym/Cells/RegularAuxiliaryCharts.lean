import PlanarNikodym.Geometry.AnalyticImplicit
import PlanarNikodym.Tame.FamilySemantics

/-! Actual centre-preserving charts at auxiliary-regular zeroes. The
implicit function, bounded connected source, continuous inverse and tame
child family are constructed here, rather than supplied as cell data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

def auxiliarySplitEquiv (d : ℕ) :
    (Parameters 2 d × ℝ) ≃L[ℝ] Parameters 2 (d + 1) :=
  ({ toFun := fun p => (p.1.1, Fin.cons p.2 p.1.2)
     invFun := fun p => ((p.1, Fin.tail p.2), p.2 0)
     left_inv := by intro p; simp only [Fin.tail_cons, Fin.cons_zero]
     right_inv := by intro p; exact Prod.ext rfl (Fin.cons_self_tail p.2)
     map_add' := by
       intro p q
       apply Prod.ext
       · rfl
       funext i
       exact Fin.cases rfl (fun _ => rfl) i
     map_smul' := by
       intro c p
       apply Prod.ext
       · rfl
       funext i
       exact Fin.cases rfl (fun _ => rfl) i } :
    (Parameters 2 d × ℝ) ≃ₗ[ℝ] Parameters 2 (d + 1)).toContinuousLinearEquiv

/-- A regular zero in an auxiliary direction admits an actual local
analytic piece of one smaller auxiliary dimension. All source closures
stay inside the original analytic domain; hence the child has the actual
R_an seed certificate as well. The final neighbourhood statement gives
local coverage of the zero locus, not just a parametrized subset of it. -/
theorem exists_regular_auxiliary_zero_piece {d : ℕ} (G : Family 2 (d + 1))
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (R : Parameters 2 d × ℝ → ℝ) (q : Parameters 2 d) (w : ℝ)
    (hp : auxiliarySplitEquiv d (q, w) ∈ G.W)
    (hR : AnalyticAt ℝ R (q, w)) (hzero : R (q, w) = 0)
    (hi : ((fderiv ℝ R (q, w)).comp
      (ContinuousLinearMap.inr ℝ (Parameters 2 d) ℝ)).IsInvertible) :
    ∃ P : AnalyticPiece G,
      P.dim = d ∧ P.family.RanTame ∧
      auxiliarySplitEquiv d (q, w) ∈ P.image ∧
      P.image ⊆ {p | R ((auxiliarySplitEquiv d).symm p) = 0} ∧
      ∀ᶠ p in 𝓝 (auxiliarySplitEquiv d (q, w)),
        R ((auxiliarySplitEquiv d).symm p) = 0 → p ∈ P.image := by
  let E := auxiliarySplitEquiv d
  obtain ⟨κ, hκ, hκq, hzeros, hiff⟩ := exists_analytic_implicit R q w hR hzero hi
  let Φ : Parameters 2 d → Parameters 2 (d + 1) := fun x => E (x, κ x)
  have hΦ (x : Parameters 2 d) (hx : AnalyticAt ℝ κ x) : AnalyticAt ℝ Φ x :=
    (E.analyticAt (x, κ x)).comp (f := fun x => (x, κ x)) (analyticAt_id.prod hx)
  have hΦq : Φ q = E (q, w) := by simp only [Φ, hκq]
  have hmap : ∀ᶠ x in 𝓝 q, Φ x ∈ G.W := by
    apply (hΦ q hκ).continuousAt.preimage_mem_nhds
    exact ho.mem_nhds (hΦq ▸ hp)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hκ.eventually_analyticAt.and (hmap.and hzeros))
  let H : Family 2 d :=
    { I := G.I
      W := ball q r
      γ := fun t x => G.γ t (Φ x) }
  have hclosure : closure H.W ⊆ closedBall q r :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  have hHa : H.IsAnalyticAtClosure := by
    intro p hp
    have hb := hball (hclosure hp.2)
    have harg : AnalyticAt ℝ (fun z : ℝ × Parameters 2 d => (z.1, Φ z.2)) p :=
      (ContinuousLinearMap.fst ℝ ℝ (Parameters 2 d)).analyticAt p |>.prod
        ((hΦ p.2 hb.1).comp ((ContinuousLinearMap.snd ℝ ℝ (Parameters 2 d)).analyticAt p))
    exact (ha (p.1, Φ p.2) ⟨hp.1, hb.2.1⟩).comp
      (f := fun z : ℝ × Parameters 2 d => (z.1, Φ z.2)) harg
  have hH : H.IsAnalytic := by
    intro p hp
    exact hHa p ⟨hp.1, subset_closure hp.2⟩
  let P : AnalyticPiece G :=
    { dim := d
      dim_le := Nat.le_succ d
      family := H
      interval_eq := rfl
      open_domain := isOpen_ball
      bounded_domain := isBounded_ball
      connected_domain := (convex_ball q r).isConnected (nonempty_ball.mpr hr)
      analytic_family := hH
      embed := Φ
      inverse := fun p => (E.symm p).1
      analytic_embed := fun x hx => hΦ x (hball (ball_subset_closedBall hx)).1
      continuous_inverse := (continuous_fst.comp E.symm.continuous).continuousOn
      left_inv := by intro x _; simp only [Φ, E.symm_apply_apply]
      keep_center := fun _ _ => rfl
      maps_to := fun x hx => (hball (ball_subset_closedBall hx)).2.1
      identity := fun _ _ _ _ => rfl }
  have htame : H.RanTame := H.ranTame_seed_ball q r rfl hHa
  refine ⟨P, rfl, htame, ?_, ?_, ?_⟩
  · exact ⟨q, mem_ball_self hr, hΦq⟩
  · rintro p ⟨x, hx, rfl⟩
    change R (E.symm (E (x, κ x))) = 0
    rw [E.symm_apply_apply]
    exact (hball (ball_subset_closedBall hx)).2.2
  · have hi' : ∀ᶠ p in 𝓝 (E (q, w)), R (E.symm p) = 0 ↔
        κ (E.symm p).1 = (E.symm p).2 := by
      have hec : ContinuousAt E.symm (E (q, w)) := E.symm.continuous.continuousAt
      have het : Tendsto E.symm (𝓝 (E (q, w))) (𝓝 (q, w)) := by
        simpa only [E.symm_apply_apply] using hec.tendsto
      exact het.eventually hiff
    have hb' : ∀ᶠ p in 𝓝 (E (q, w)), (E.symm p).1 ∈ ball q r := by
      have hproj : ContinuousAt (fun p => (E.symm p).1) (E (q, w)) :=
        (continuous_fst.comp E.symm.continuous).continuousAt
      apply hproj.preimage_mem_nhds
      rw [E.symm_apply_apply]
      exact isOpen_ball.mem_nhds (mem_ball_self hr)
    filter_upwards [hi', hb'] with p hip hbp hz
    refine ⟨(E.symm p).1, hbp, ?_⟩
    change E ((E.symm p).1, κ (E.symm p).1) = p
    rw [hip.mp hz]
    exact E.apply_symm_apply p

theorem real_clm_isInvertible_of_apply_one_ne_zero (L : ℝ →L[ℝ] ℝ)
    (hL : L 1 ≠ 0) : L.IsInvertible := by
  have hform (x : ℝ) : L x = x * L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul x (1 : ℝ)
  have hinj : Function.Injective L := by
    intro x y hxy
    exact mul_right_cancel₀ hL ((hform x).symm.trans (hxy.trans (hform y)))
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨y / L 1, ?_⟩
    rw [hform, div_mul_cancel₀ y hL]
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

/-- Scalar, directly checkable regularity criterion for the chart theorem:
the selected auxiliary partial derivative is nonzero. -/
theorem exists_auxiliary_partial_zero_piece {d : ℕ} (G : Family 2 (d + 1))
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (R : Parameters 2 d × ℝ → ℝ) (q : Parameters 2 d) (w : ℝ)
    (hp : auxiliarySplitEquiv d (q, w) ∈ G.W)
    (hR : AnalyticAt ℝ R (q, w)) (hzero : R (q, w) = 0)
    (hpartial : fderiv ℝ R (q, w) (0, 1) ≠ 0) :
    ∃ P : AnalyticPiece G,
      P.dim = d ∧ P.family.RanTame ∧
      auxiliarySplitEquiv d (q, w) ∈ P.image ∧
      P.image ⊆ {p | R ((auxiliarySplitEquiv d).symm p) = 0} ∧
      ∀ᶠ p in 𝓝 (auxiliarySplitEquiv d (q, w)),
        R ((auxiliarySplitEquiv d).symm p) = 0 → p ∈ P.image := by
  apply exists_regular_auxiliary_zero_piece G ho ha R q w hp hR hzero
  exact real_clm_isInvertible_of_apply_one_ne_zero _ hpartial

/-- Compact auxiliary-regular zero loci have an actual finite cover by
the constructed tame, centre-preserving, dimension-dropping charts.
The cover can overlap; disjoint global cells require further geometry. -/
theorem exists_finite_regular_auxiliary_zero_cover {d : ℕ} (G : Family 2 (d + 1))
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (R : Parameters 2 d × ℝ → ℝ)
    {K : Set (Parameters 2 (d + 1))} (hK : IsCompact K) (hKW : K ⊆ G.W)
    (hR : ∀ p ∈ K, AnalyticAt ℝ R ((auxiliarySplitEquiv d).symm p))
    (hzero : ∀ p ∈ K, R ((auxiliarySplitEquiv d).symm p) = 0)
    (hpartial : ∀ p ∈ K, fderiv ℝ R ((auxiliarySplitEquiv d).symm p) (0, 1) ≠ 0) :
    ∃ s : Finset K, ∃ P : s → AnalyticPiece G,
      (∀ i, (P i).dim = d ∧ (P i).family.RanTame ∧
        (P i).image ⊆ {p | R ((auxiliarySplitEquiv d).symm p) = 0}) ∧
      K ⊆ ⋃ i, (P i).image := by
  classical
  let E := auxiliarySplitEquiv d
  have hlocal (p : K) :
      ∃ P : AnalyticPiece G, P.dim = d ∧ P.family.RanTame ∧
        P.image ⊆ {p | R (E.symm p) = 0} ∧
        ∀ᶠ y in 𝓝 p.1, R (E.symm y) = 0 → y ∈ P.image := by
    have he : auxiliarySplitEquiv d ((E.symm p.1).1, (E.symm p.1).2) = p.1 :=
      E.apply_symm_apply p.1
    obtain ⟨P, hd, ht, _, hz, hloc⟩ := exists_auxiliary_partial_zero_piece G ho ha R
      (E.symm p.1).1 (E.symm p.1).2
      (by rw [he]; exact hKW p.2)
      (hR p p.2) (hzero p p.2) (hpartial p p.2)
    refine ⟨P, hd, ht, hz, ?_⟩
    rwa [he] at hloc
  choose P hd ht hz hloc using hlocal
  have hopen (p : K) : ∃ O : Set (Parameters 2 (d + 1)),
      IsOpen O ∧ p.1 ∈ O ∧ ∀ y ∈ O, R (E.symm y) = 0 → y ∈ (P p).image := by
    obtain ⟨O, hOsub, hOo, hpO⟩ := _root_.eventually_nhds_iff.mp (hloc p)
    exact ⟨O, hOo, hpO, fun y hy => hOsub y hy⟩
  choose O hOo hpO hOsub using hopen
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover O hOo (by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpO ⟨p, hp⟩⟩)
  refine ⟨s, fun i => P i.1, fun i => ⟨hd i.1, ht i.1, hz i.1⟩, ?_⟩
  intro p hp
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hs hp)
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, hOsub i p hpi (hzero p hp)⟩

end PlanarNikodym
