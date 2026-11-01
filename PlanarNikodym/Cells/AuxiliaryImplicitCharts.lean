import PlanarNikodym.Cells.RegularAuxiliaryCharts
import PlanarNikodym.Cells.AuxiliarySingularJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

def auxiliaryCoordinateSplitEquiv {d : ℕ} (j : Fin (d + 1)) :
    (Parameters 2 d × ℝ) ≃L[ℝ] Parameters 2 (d + 1) :=
  ({ toFun := fun p => (p.1.1, j.insertNth p.2 p.1.2)
     invFun := fun p => ((p.1, j.removeNth p.2), p.2 j)
     left_inv := by intro p; simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
     right_inv := by intro p; exact Prod.ext rfl (Fin.insertNth_self_removeNth j p.2)
     map_add' := by
       intro p q
       apply Prod.ext
       · rfl
       · funext i
         by_cases hi : i = j
         · subst i; simp
         · by_cases hij : i < j <;> simp [Fin.insertNth, Fin.succAboveCases, hi, hij]
     map_smul' := by
       intro c p
       apply Prod.ext
       · rfl
       · funext i
         by_cases hi : i = j <;> simp [Fin.insertNth, Fin.succAboveCases, hi] } :
    (Parameters 2 d × ℝ) ≃ₗ[ℝ] Parameters 2 (d + 1)).toContinuousLinearEquiv

theorem auxiliaryCoordinateSplitEquiv_vertical {d : ℕ} (j : Fin (d + 1)) :
    auxiliaryCoordinateSplitEquiv j (0, 1) = (0, Pi.single j 1) := by
  apply Prod.ext
  · rfl
  · funext i
    by_cases hi : i = j <;>
      simp [auxiliaryCoordinateSplitEquiv, hi]

/-- The implicit construction in any actual centre-preserving linear
frame, with its source and child tameness constructed from the germ. -/
theorem exists_auxiliary_zero_piece_in_frame {d : ℕ} (G : Family 2 (d + 1))
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (E : (Parameters 2 d × ℝ) ≃L[ℝ] Parameters 2 (d + 1))
    (hE : ∀ x t, (E (x, t)).1 = x.1)
    (R : Parameters 2 d × ℝ → ℝ) (q : Parameters 2 d) (w : ℝ)
    (hp : E (q, w) ∈ G.W)
    (hR : AnalyticAt ℝ R (q, w)) (hzero : R (q, w) = 0)
    (hi : ((fderiv ℝ R (q, w)).comp
      (ContinuousLinearMap.inr ℝ (Parameters 2 d) ℝ)).IsInvertible) :
    ∃ P : AnalyticPiece G,
      P.dim = d ∧ P.family.RanTame ∧ E (q, w) ∈ P.image ∧
      P.image ⊆ {p | R (E.symm p) = 0} ∧
      ∀ᶠ p in 𝓝 (E (q, w)), R (E.symm p) = 0 → p ∈ P.image := by
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
      keep_center := fun x _ => hE x (κ x)
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

/-- The nonzero auxiliary coordinate can be arbitrary. No a priori
permutation of the original family is required. -/
theorem exists_regular_auxiliary_coordinate_zero_piece {d : ℕ}
    (G : Family 2 (d + 1)) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (F : Parameters 2 (d + 1) → ℝ) (hF : AnalyticOnNhd ℝ F G.W)
    {p : Parameters 2 (d + 1)} (hp : p ∈ G.W) (hzero : F p = 0)
    (j : Fin (d + 1)) (hpartial : fderiv ℝ F p (0, Pi.single j 1) ≠ 0) :
    ∃ P : AnalyticPiece G, P.dim = d ∧ P.family.RanTame ∧
      p ∈ P.image ∧ P.image ⊆ {y | F y = 0} ∧
      ∀ᶠ y in 𝓝 p, F y = 0 → y ∈ P.image := by
  let E := auxiliaryCoordinateSplitEquiv j
  let q := (E.symm p).1
  let w := (E.symm p).2
  let R := F ∘ E
  have he : E (q, w) = p := E.apply_symm_apply p
  have hFp : AnalyticAt ℝ F (E (q, w)) := by rw [he]; exact hF p hp
  have hR : AnalyticAt ℝ R (q, w) := hFp.comp (f := E) (E.analyticAt (q, w))
  have hRzero : R (q, w) = 0 := by change F (E (q, w)) = 0; rw [he]; exact hzero
  have hRp : fderiv ℝ R (q, w) (0, 1) ≠ 0 := by
    rw [fderiv_comp (q, w) hFp.differentiableAt E.differentiableAt,
      E.hasFDerivAt.fderiv]
    have he01 : E (0, 1) = (0, Pi.single j 1) := auxiliaryCoordinateSplitEquiv_vertical j
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      he01, he] using hpartial
  obtain ⟨P, hd, ht, hpP, hPzero, hlocal⟩ := exists_auxiliary_zero_piece_in_frame G ho ha E
    (fun _ _ => rfl) R q w (he ▸ hp) hR hRzero
    (real_clm_isInvertible_of_apply_one_ne_zero _ hRp)
  refine ⟨P, hd, ht, he ▸ hpP, ?_, ?_⟩
  · intro y hy
    have hz : R (E.symm y) = 0 := hPzero hy
    change F (E (E.symm y)) = 0 at hz
    change F y = 0
    simpa only [E.apply_symm_apply] using hz
  · rw [he] at hlocal
    filter_upwards [hlocal] with y hy hFy
    apply hy
    change F (E (E.symm y)) = 0
    simpa only [E.apply_symm_apply] using hFy

/-- All zeroes, including auxiliary-singular ones, either have a flat
auxiliary fibre or lie in an actual centre-preserving lower-dimensional
tame chart of a coordinate-derivative hypersurface. The chart need not
lie in the original zero set; it lies in the specified derivative zero
set, and no global finite/disjoint-cover conclusion is asserted. -/
theorem auxiliary_zero_flat_or_lower_piece {d : ℕ}
    (G : Family 2 (d + 1)) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (F : Parameters 2 (d + 1) → ℝ) (hF : AnalyticOnNhd ℝ F G.W)
    {p : Parameters 2 (d + 1)} (hp : p ∈ G.W) (hzero : F p = 0) :
    (∀ᶠ u in 𝓝 p.2, F (p.1, u) = 0) ∨
      ∃ P : AnalyticPiece G, P.dim = d ∧ P.family.RanTame ∧ p ∈ P.image ∧
        ∃ (k : ℕ) (s : Fin k → Fin (d + 1)),
          P.image ⊆ {y | auxiliaryJet F k s y = 0} := by
  rcases auxiliary_zero_flat_or_regularJet ho hF hp hzero with hflat | ⟨k, s, j, hz, hreg⟩
  · exact Or.inl hflat
  · obtain ⟨P, hd, ht, hpP, hPzero, _⟩ := exists_regular_auxiliary_coordinate_zero_piece
      G ho ha (auxiliaryJet F k s) (auxiliaryJet_analytic ho hF k s) hp hz j hreg
    exact Or.inr ⟨P, hd, ht, hpP, k, s, hPzero⟩

end PlanarNikodym
