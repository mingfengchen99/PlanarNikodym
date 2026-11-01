import PlanarNikodym.Geometry.SemianalyticComponentUnions
import PlanarNikodym.Tame.DefinableContinuousImageComponents

/-! Actual source witnesses for components of a continuous image. The
source is constructed as a union of source components; it is not the
usually non-semianalytic full inverse image of the target component. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem image_sUnion_components_meeting_target_component
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (F : X → Y) (hF : ContinuousOn F A) (y : Y) :
    F '' (⋃₀ {C ∈ componentDomains A |
      (F '' C ∩ _root_.connectedComponentIn (F '' A) y).Nonempty}) =
        _root_.connectedComponentIn (F '' A) y := by
  classical
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨C, ⟨hCA, hmeet⟩, hxC⟩ := mem_sUnion.mp hx
    obtain ⟨a, ha, hC⟩ := hCA
    have hsub : C ⊆ A := hC ▸ connectedComponentIn_subset A a
    have hconn : IsPreconnected (F '' C) := by
      apply IsPreconnected.image _ F (hF.mono hsub)
      rw [hC]
      exact isPreconnected_connectedComponentIn
    obtain ⟨z, hzC, hz⟩ := hmeet
    have he := connectedComponentIn_eq hz
    rw [he]
    exact hconn.subset_connectedComponentIn hzC (image_mono hsub)
      (mem_image_of_mem F hxC)
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := connectedComponentIn_subset (F '' A) y hz
    refine ⟨x, mem_sUnion.mpr ⟨_root_.connectedComponentIn A x, ?_, mem_connectedComponentIn hx⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, F x, mem_image_of_mem F (mem_connectedComponentIn hx), hz⟩

theorem LocallySemianalytic.exists_component_image_source
    {n : ℕ} {Y : Type*} [TopologicalSpace Y] {A : Set (Fin n → ℝ)}
    (hA : LocallySemianalytic A) (hb : Bornology.IsBounded A)
    (F : (Fin n → ℝ) → Y) (hF : ContinuousOn F A) (y : Y) :
    ∃ B : Set (Fin n → ℝ), B ⊆ A ∧ LocallySemianalytic B ∧
      Bornology.IsBounded B ∧
      F '' B = _root_.connectedComponentIn (F '' A) y := by
  let J := {C ∈ componentDomains A |
    (F '' C ∩ _root_.connectedComponentIn (F '' A) y).Nonempty}
  have hJA : J ⊆ componentDomains A := fun _ h => h.1
  have hsub : ⋃₀ J ⊆ A := by
    intro x hx
    obtain ⟨C, hCJ, hxC⟩ := mem_sUnion.mp hx
    obtain ⟨a, _, he⟩ := hJA hCJ
    exact connectedComponentIn_subset A a (he ▸ hxC)
  exact ⟨⋃₀ J, hsub, hA.sUnion_components J hJA, hb.subset hsub,
    image_sUnion_components_meeting_target_component F hF y⟩

theorem LocallySemianalytic.exists_component_image_source_with_closure
    {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {A : Set (Fin n → ℝ)} (hA : LocallySemianalytic A)
    (hb : Bornology.IsBounded A) (F : (Fin n → ℝ) → Y)
    (hF : ContinuousOn F (closure A)) (y : Y) :
    ∃ B : Set (Fin n → ℝ), B ⊆ A ∧ LocallySemianalytic B ∧
      Bornology.IsBounded B ∧ F '' B = _root_.connectedComponentIn (F '' A) y ∧
      F '' closure B = closure (_root_.connectedComponentIn (F '' A) y) := by
  obtain ⟨B, hBA, hB, hbB, he⟩ := hA.exists_component_image_source hb F
    (hF.mono subset_closure) y
  refine ⟨B, hBA, hB, hbB, he, ?_⟩
  rw [← he]
  have hFc : ContinuousOn F (closure B) := hF.mono (closure_mono hBA)
  apply Subset.antisymm
  · exact hFc.image_closure
  · exact closure_minimal (image_mono subset_closure)
      (hbB.isCompact_closure.image_of_continuousOn hFc).isClosed

end PlanarNikodym
