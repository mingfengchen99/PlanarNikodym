import PlanarNikodym.Tame.FiniteAnalyticGraphs
import PlanarNikodym.Cells.RankDecomposition

noncomputable section
open Set Metric

namespace PlanarNikodym

abbrev RanParameterIndex (d : ℕ) := Fin 2 ⊕ Fin d

def ranParameterEquiv (d : ℕ) : (RanParameterIndex d → ℝ) ≃L[ℝ] Parameters 2 d :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin d) ℝ ℝ).toContinuousLinearEquiv

def ranTimeParameterEquiv (d : ℕ) :
    (Option (RanParameterIndex d) → ℝ) ≃L[ℝ] (ℝ × Parameters 2 d) :=
  ({ toFun := fun x => (x none, (fun i => x (some (.inl i)), fun i => x (some (.inr i))))
     invFun := fun x i => Option.elim i x.1 (Sum.elim x.2.1 x.2.2)
     left_inv := by intro x; funext i; cases i with
       | none => rfl
       | some i => cases i <;> rfl
     right_inv := by intro x; rfl
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } :
    (Option (RanParameterIndex d) → ℝ) ≃ₗ[ℝ] (ℝ × Parameters 2 d)).toContinuousLinearEquiv

/-- Concrete tame semantics: the parameter domain and the actual curve
graph over `I × W` are definable in the restricted analytic real structure.
Analyticity is an independent assumption, absent from this predicate. -/
def Family.RanTame {d : ℕ} (G : Family 2 d) : Prop :=
  RanDefinable (ranParameterEquiv d ⁻¹' G.W) ∧
    RanDefinableOn (fun x => G.γ (ranTimeParameterEquiv d x).1
      (ranTimeParameterEquiv d x).2)
      (ranTimeParameterEquiv d ⁻¹' (G.I.carrier ×ˢ G.W))

theorem ranDefinable_timeParameterDomain {d : ℕ} (G : Family 2 d)
    (hW : RanDefinable (ranParameterEquiv d ⁻¹' G.W)) :
    RanDefinable (ranTimeParameterEquiv d ⁻¹' (G.I.carrier ×ˢ G.W)) := by
  have ht : RanDefinable {x : Option (RanParameterIndex d) → ℝ |
      G.I.left ≤ x none ∧ x none ≤ G.I.right} :=
    (ranDefinable_le (ranDefinableFun_const G.I.left) (ranDefinableFun_coordinate none)).inter
      (ranDefinable_le (ranDefinableFun_coordinate none) (ranDefinableFun_const G.I.right))
  exact ht.inter (hW.preimage_comp some)

theorem Family.ranTame_of_definable_domain {d : ℕ} (G : Family 2 d)
    (hW : RanDefinable (ranParameterEquiv d ⁻¹' G.W))
    (hb : Bornology.IsBounded G.W) (ha : G.IsAnalyticAtClosure) : G.RanTame := by
  let E := ranTimeParameterEquiv d
  have hc : IsCompact (E.symm '' (G.I.carrier ×ˢ closure G.W)) :=
    (isCompact_Icc.prod hb.isCompact_closure).image E.symm.continuous
  have hf : AnalyticOnNhd ℝ (fun x => G.γ (E x).1 (E x).2)
      (E.symm '' (G.I.carrier ×ˢ closure G.W)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hg : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
        (E (E.symm x)) := by simpa only [E.apply_symm_apply] using ha x hx
    exact hg.comp (f := E) (E.analyticAt (E.symm x))
  obtain ⟨U, _, hKU, _, hfU⟩ := exists_ranDefinableOn_nhds_of_compact_finite hc hf
  refine ⟨hW, hfU.restrict (ranDefinable_timeParameterDomain G hW) ?_⟩
  intro x hx
  apply hKU
  exact ⟨E x, ⟨hx.1, subset_closure hx.2⟩, E.symm_apply_apply x⟩

theorem ranDefinable_parameter_ball (d : ℕ) (c : Parameters 2 d) (r : ℝ) :
    RanDefinable (ranParameterEquiv d ⁻¹' ball c r) := by
  change RanDefinable
    ((IsometryEquiv.sumArrowIsometryEquivProdArrow (α := Fin 2) (β := Fin d)) ⁻¹' ball c r)
  rw [IsometryEquiv.preimage_ball]
  exact ranDefinable_ball _ r

/-- The actual seed required by `ConnectedCellInput.seed_ball`, with
`tame d G := G.RanTame`. No cell theorem is assumed. -/
theorem Family.ranTame_seed_ball {d : ℕ} (G : Family 2 d)
    (c : Parameters 2 d) (r : ℝ) (hW : G.W = ball c r)
    (ha : G.IsAnalyticAtClosure) : G.RanTame := by
  apply G.ranTame_of_definable_domain
  · rw [hW]
    exact ranDefinable_parameter_ball d c r
  · rw [hW]
    exact isBounded_ball
  · exact ha

theorem ranDefinable_parameter_analytic_sublevel {d : ℕ} {W : Set (Parameters 2 d)}
    {f : Parameters 2 d → ℝ} (hb : Bornology.IsBounded W)
    (hf : AnalyticOnNhd ℝ f (closure W)) (hW : W = {p | f p < 0}) :
    RanDefinable (ranParameterEquiv d ⁻¹' W) := by
  let E := ranParameterEquiv d
  have he : closure (E ⁻¹' W) = E.symm '' closure W := by
    exact (E.toHomeomorph.preimage_closure W).symm.trans
      (E.toEquiv.image_symm_eq_preimage _).symm
  apply ranDefinable_bounded_analytic_sublevel_finite
  · rw [he]
    exact hb.isCompact_closure.image E.symm.continuous
  · rw [he]
    rintro _ ⟨x, hx, rfl⟩
    have hfx : AnalyticAt ℝ f (E (E.symm x)) := by simpa only [E.apply_symm_apply] using hf x hx
    exact hfx.comp (f := E) (E.analyticAt (E.symm x))
  · rw [hW]
    rfl

/-- Both domain alternatives in the existing `AnalyticCellInput.seed`
have concrete restricted analytic certificates. -/
theorem Family.ranTame_seed {d : ℕ} (G : Family 2 d)
    (hD : AnalyticParameterDomain G) (ha : G.IsAnalyticAtClosure) : G.RanTame := by
  rcases hD with ⟨_, hb, hball | hsub⟩
  · obtain ⟨c, r, _, hW⟩ := hball
    exact G.ranTame_seed_ball c r hW ha
  · obtain ⟨f, hf, hW⟩ := hsub
    exact G.ranTame_of_definable_domain
      (ranDefinable_parameter_analytic_sublevel hb hf hW) hb ha

end PlanarNikodym
