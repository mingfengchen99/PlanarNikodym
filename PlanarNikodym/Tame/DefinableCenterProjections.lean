import PlanarNikodym.Tame.FamilySemantics
import PlanarNikodym.Tame.DefinableTopology

noncomputable section
open Set

namespace PlanarNikodym

theorem ranDefinable_parameter_closure {d : ℕ} {S : Set (Parameters 2 d)}
    (hS : RanDefinable (ranParameterEquiv d ⁻¹' S)) :
    RanDefinable (ranParameterEquiv d ⁻¹' closure S) := by
  change RanDefinable ((ranParameterEquiv d).toHomeomorph ⁻¹' closure S)
  rw [(ranParameterEquiv d).toHomeomorph.preimage_closure]
  exact RanDefinable.closure hS

/-- The actual centre image is a finite coordinate projection. No
measurability or nullity assertion is hidden in this statement. -/
theorem ranDefinable_center_image {d : ℕ} {S : Set (Parameters 2 d)}
    (hS : RanDefinable (ranParameterEquiv d ⁻¹' S)) :
    RanDefinable (Prod.fst '' S) := by
  let E := ranParameterEquiv d
  convert hS.image_comp Sum.inl using 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨E.symm p, ?_, ?_⟩
    · change E (E.symm p) ∈ S
      simpa only [E.apply_symm_apply] using hp
    · change (E (E.symm p)).1 = p.1
      rw [E.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨E x, hx, rfl⟩

theorem ranDefinable_center_image_closure {d : ℕ} {S : Set (Parameters 2 d)}
    (hS : RanDefinable (ranParameterEquiv d ⁻¹' S)) :
    RanDefinable (closure (Prod.fst '' S)) :=
  RanDefinable.closure (ranDefinable_center_image hS)

end PlanarNikodym
