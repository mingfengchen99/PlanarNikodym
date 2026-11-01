import PlanarNikodym.Geometry.FiniteConnectedSignComponents
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual finite component families under continuous images and inverse
homeomorphic coordinates, including empty sets and points outside the domain. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem components_finite_continuous_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (hA : (componentDomains A).Finite) (F : X → Y) (hF : ContinuousOn F A) :
    (componentDomains (F '' A)).Finite := by
  classical
  letI : Fintype (componentDomains A) := hA.fintype
  let C (j : componentDomains A) := F '' j.val
  have hsub (j : componentDomains A) : j.val ⊆ A := by
    obtain ⟨x, _, he⟩ := j.property
    rw [he]
    exact connectedComponentIn_subset A x
  apply components_finite_of_finite_preconnected_cover C
  · intro j
    apply IsPreconnected.image _ F (hF.mono (hsub j))
    obtain ⟨x, _, he⟩ := j.property
    rw [he]
    exact isPreconnected_connectedComponentIn
  · exact fun j => image_mono (hsub j)
  · rintro y ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨⟨connectedComponentIn A x, x, hx, rfl⟩,
      x, mem_connectedComponentIn hx, rfl⟩

theorem components_finite_of_homeomorph_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set Y) (hA : (componentDomains (e ⁻¹' A)).Finite) :
    (componentDomains A).Finite := by
  have h := components_finite_continuous_image hA e e.continuous.continuousOn
  rwa [e.image_preimage] at h

theorem preimage_connectedComponentIn_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set Y) (x : Y) :
    e ⁻¹' connectedComponentIn A x = connectedComponentIn (e ⁻¹' A) (e.symm x) := by
  by_cases hx : x ∈ A
  · have h := e.symm.image_connectedComponentIn hx
    simpa only [e.image_symm] using h
  · have hx' : e.symm x ∉ e ⁻¹' A := by
      simpa only [mem_preimage, e.apply_symm_apply] using hx
    rw [connectedComponentIn_eq_empty hx, connectedComponentIn_eq_empty hx', preimage_empty]

end PlanarNikodym
