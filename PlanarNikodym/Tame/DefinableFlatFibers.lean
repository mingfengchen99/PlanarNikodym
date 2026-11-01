import PlanarNikodym.Cells.AnalyticFiberExceptions
import PlanarNikodym.Tame.FamilySemantics
import PlanarNikodym.Tame.DefinableTopology

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory

namespace PlanarNikodym

theorem ranDefinable_parameter_product {d : ℕ}
    {V : Set (Base 2)} {U : Set (Aux d)}
    (hV : RanDefinable V) (hU : RanDefinable U) :
    RanDefinable (ranParameterEquiv d ⁻¹' (V ×ˢ U)) :=
  (hV.preimage_comp Sum.inl).inter (hU.preimage_comp Sum.inr)

/-- Local flatness of a fibre has a genuine finite first-order formula:
analytic continuation turns it into universal vanishing on the connected
auxiliary patch. -/
theorem ranDefinable_flatFiberCenters {d : ℕ}
    {f : Parameters 2 d → ℝ} {V : Set (Base 2)} {U : Set (Aux d)}
    (hV : RanDefinable V) (hU : RanDefinable U) (hoU : IsOpen U) (hcU : IsConnected U)
    (ha : AnalyticOnNhd ℝ f (V ×ˢ U))
    (hf : RanDefinableOn (f ∘ ranParameterEquiv d)
      (ranParameterEquiv d ⁻¹' (V ×ˢ U))) :
    RanDefinable (flatFiberCenters f V U) := by
  let D := ranParameterEquiv d ⁻¹' (V ×ˢ U)
  let F := ranZeroExtension (f ∘ ranParameterEquiv d) D
  have hD : RanDefinable D := ranDefinable_parameter_product hV hU
  have hzero : RanDefinable {w : RanParameterIndex d → ℝ | F w = 0} :=
    (hf.zeroExtension hD).setOf_eq (ranDefinableFun_const 0)
  have hall := ((hU.preimage_comp Sum.inr).himp hzero).forall_of_finite
  convert hV.inter hall using 1
  ext z
  rw [flatFiberCenters_iff_all ha hoU hcU z]
  apply and_congr_right
  intro hz
  change (∀ u ∈ U, f (z, u) = 0) ↔
    ∀ u : Aux d, u ∈ U → F (Sum.elim z u) = 0
  apply forall_congr'
  intro u
  apply imp_congr_right
  intro hu
  have hzu : Sum.elim z u ∈ D := ⟨hz, hu⟩
  simp only [F, ranZeroExtension, if_pos hzu]
  rfl

/-- The flat-fibre branch supplies an actual definable closed null
exceptional set on compact centre patches. -/
theorem exists_ranDefinable_closed_null_flat_fiber_exception {d : ℕ}
    {f : Parameters 2 d → ℝ} {V : Set (Base 2)} {U : Set (Aux d)}
    (hV : RanDefinable V) (hU : RanDefinable U)
    (hoV : IsOpen V) (hoU : IsOpen U) (hcV : IsConnected V) (hcU : IsConnected U)
    (ha : AnalyticOnNhd ℝ f (V ×ˢ U))
    (hf : RanDefinableOn (f ∘ ranParameterEquiv d)
      (ranParameterEquiv d ⁻¹' (V ×ˢ U)))
    (hne : ∃ z ∈ V, ∃ u ∈ U, f (z, u) ≠ 0)
    {K : Set (Base 2)} (hK : IsCompact K) (hKV : K ⊆ V) (hKd : RanDefinable K) :
    ∃ E : Set (Base 2), RanDefinable E ∧ IsClosed E ∧ volume E = 0 ∧
      closure (K ∩ flatFiberCenters f V U) ⊆ E := by
  refine ⟨closure (K ∩ flatFiberCenters f V U), ?_, isClosed_closure, ?_, Subset.rfl⟩
  · exact RanDefinable.closure
      (hKd.inter (ranDefinable_flatFiberCenters hV hU hoU hcU ha hf))
  · exact flatFiberCenters_closure_null_on_compact hoV hcV.isPreconnected hcU.isPreconnected
      ha hne hK hKV

end PlanarNikodym
