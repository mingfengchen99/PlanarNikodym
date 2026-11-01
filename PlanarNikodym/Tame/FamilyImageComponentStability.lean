import PlanarNikodym.Geometry.ContinuousImageComponentSources
import PlanarNikodym.Tame.FamilyStability
import PlanarNikodym.Geometry.FiniteComponentImages

/-! Component stability for actual finite-dimensional bounded semianalytic
image representations. The representation is geometric data, independent
of the first-order tame predicate. No general R_an elimination theorem is
claimed by this result. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem Family.ranTame_components_of_semianalytic_image
    {d n : ℕ} (G : Family 2 d) (hG : G.RanTame)
    (A : Set (Fin n → ℝ)) (hA : LocallySemianalytic A) (hb : Bornology.IsBounded A)
    (F : (Fin n → ℝ) → (RanParameterIndex d → ℝ))
    (hF : ContinuousOn F A) (hFd : ∀ i, RanDefinableOn (fun x => F x i) A)
    (himage : F '' A = (ranParameterEquiv d) ⁻¹' G.W) :
    (componentDomains G.W).Finite ∧
      ∀ p, (G.restrictTo (_root_.connectedComponentIn G.W p)).RanTame := by
  let e := ranParameterEquiv d
  obtain ⟨hf, hd⟩ := hA.finite_definable_image_components hb F hF hFd
  rw [himage] at hf hd
  refine ⟨components_finite_of_homeomorph_preimage e.toHomeomorph G.W hf, ?_⟩
  intro p
  apply hG.restrictTo _ (connectedComponentIn_subset G.W p)
  have he := preimage_connectedComponentIn_homeomorph e.toHomeomorph G.W p
  change RanDefinable (e.toHomeomorph ⁻¹' _root_.connectedComponentIn G.W p)
  rw [he]
  exact hd (e.symm p)

theorem Family.ranTame_components_of_analytic_image
    {d n : ℕ} (G : Family 2 d) (hG : G.RanTame)
    (A : Set (Fin n → ℝ)) (hA : LocallySemianalytic A) (hb : Bornology.IsBounded A)
    (F : (Fin n → ℝ) → (RanParameterIndex d → ℝ))
    (hF : AnalyticOnNhd ℝ F (closure A))
    (himage : F '' A = (ranParameterEquiv d) ⁻¹' G.W) :
    (componentDomains G.W).Finite ∧
      ∀ p, (G.restrictTo (_root_.connectedComponentIn G.W p)).RanTame := by
  apply G.ranTame_components_of_semianalytic_image hG A hA hb F
    (hF.continuousOn.mono subset_closure) _ himage
  intro i
  exact ranDefinableOn_of_analyticOnNhd_compact_closure
    (hA.ranDefinable_of_bounded hb) hb.isCompact_closure
    (fun x hx => analyticAt_pi_iff.mp (hF x hx) i)

end PlanarNikodym
