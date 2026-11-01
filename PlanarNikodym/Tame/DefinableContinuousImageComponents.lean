import PlanarNikodym.Tame.DefinableSemianalyticComponents
import PlanarNikodym.Tame.DefinableTopology

/-! Continuous R_an maps of bounded semianalytic sets have genuinely finite
R_an-definable components. Every target component is assembled from the
finite images of actual source components, not postulated definable. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem ranDefinable_component_of_finite_preconnected_cover
    {ι : Type*} [Finite ι] {κ : Type*} [Fintype κ] {A : Set (ι → ℝ)} (C : κ → Set (ι → ℝ))
    (hC : ∀ j, IsPreconnected (C j)) (hsub : ∀ j, C j ⊆ A)
    (hcover : A ⊆ ⋃ j, C j) (hdef : ∀ j, RanDefinable (C j)) (x : ι → ℝ) :
    RanDefinable (_root_.connectedComponentIn A x) := by
  rw [component_eq_iUnion_of_finite_preconnected_cover C hC hsub hcover x]
  exact Set.definable_iUnion_of_finite
    (fun j : {j : κ // (C j ∩ _root_.connectedComponentIn A x).Nonempty} => hdef j.val)

theorem LocallySemianalytic.finite_definable_image_components
    {n : ℕ} {ι : Type*} [Fintype ι] {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) (F : (Fin n → ℝ) → (ι → ℝ))
    (hF : ContinuousOn F A) (hFd : ∀ i, RanDefinableOn (fun x => F x i) A) :
    (componentDomains (F '' A)).Finite ∧
      ∀ y, RanDefinable (_root_.connectedComponentIn (F '' A) y) := by
  classical
  letI : Fintype (componentDomains A) := (hA.components_finite_of_bounded hb).fintype
  let C (j : componentDomains A) := F '' j.val
  have hjsub (j : componentDomains A) : j.val ⊆ A := by
    obtain ⟨x, _, hj⟩ := j.property
    rw [hj]
    exact connectedComponentIn_subset A x
  have hconn (j : componentDomains A) : IsPreconnected (C j) := by
    obtain ⟨x, _, hj⟩ := j.property
    apply IsPreconnected.image _ F (hF.mono (hjsub j))
    rw [hj]
    exact isPreconnected_connectedComponentIn
  have hsub (j : componentDomains A) : C j ⊆ F '' A := image_mono (hjsub j)
  have hcover : F '' A ⊆ ⋃ j : componentDomains A, C j := by
    rintro y ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨⟨_root_.connectedComponentIn A x, x, hx, rfl⟩,
      x, mem_connectedComponentIn hx, rfl⟩
  have hdef (j : componentDomains A) : RanDefinable (C j) := by
    have hjd := hA.ranDefinable_componentDomain hb j.property
    exact ranDefinable_image_on hjd (fun i => (hFd i).restrict hjd (hjsub j))
  exact ⟨components_finite_of_finite_preconnected_cover C hconn hsub hcover,
    fun y => ranDefinable_component_of_finite_preconnected_cover C hconn hsub hcover hdef y⟩

theorem LocallySemianalytic.finite_definable_analytic_image_components
    {n : ℕ} {ι : Type*} [Fintype ι] {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) (F : (Fin n → ℝ) → (ι → ℝ))
    (hF : AnalyticOnNhd ℝ F (closure A)) :
    (componentDomains (F '' A)).Finite ∧
      ∀ y, RanDefinable (_root_.connectedComponentIn (F '' A) y) := by
  apply hA.finite_definable_image_components hb F
    (hF.continuousOn.mono subset_closure)
  intro i
  exact ranDefinableOn_of_analyticOnNhd_compact_closure
    (hA.ranDefinable_of_bounded hb) hb.isCompact_closure
    (fun x hx => analyticAt_pi_iff.mp (hF x hx) i)

end PlanarNikodym
