import PlanarNikodym.Geometry.AnalyticZeroNullity

/-! Flat auxiliary fibres have a genuine closed-null centre envelope on
compact centre patches. The envelope is a zero set of an actual frozen
slice, whose nontriviality is proved rather than assumed as a new Input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology

namespace PlanarNikodym

def flatFiberCenters {d : ℕ} (f : Parameters 2 d → ℝ)
    (V : Set (Base 2)) (U : Set (Aux d)) : Set (Base 2) :=
  {z | z ∈ V ∧ ∃ u ∈ U, ∀ᶠ v in 𝓝 u, f (z, v) = 0}

theorem flatFiberCenters_subset_frozen_zero {d : ℕ}
    {f : Parameters 2 d → ℝ} {V : Set (Base 2)} {U : Set (Aux d)}
    (ha : AnalyticOnNhd ℝ f (V ×ˢ U)) (hU : IsPreconnected U)
    {u₀ : Aux d} (hu₀ : u₀ ∈ U) :
    flatFiberCenters f V U ⊆ {z | z ∈ V ∧ f (z, u₀) = 0} := by
  rintro z ⟨hz, u, hu, hflat⟩
  have hau : AnalyticOnNhd ℝ (fun v => f (z, v)) U := by
    intro v hv
    exact (ha (z, v) ⟨hz, hv⟩).comp (f := fun v => (z, v))
      (analyticAt_const.prod analyticAt_id)
  have he := hau.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    hU hu hflat
  exact ⟨hz, he hu₀⟩

theorem flatFiberCenters_iff_all {d : ℕ}
    {f : Parameters 2 d → ℝ} {V : Set (Base 2)} {U : Set (Aux d)}
    (ha : AnalyticOnNhd ℝ f (V ×ˢ U)) (hoU : IsOpen U)
    (hU : IsConnected U) (z : Base 2) :
    z ∈ flatFiberCenters f V U ↔ z ∈ V ∧ ∀ u ∈ U, f (z, u) = 0 := by
  constructor
  · intro hz
    exact ⟨hz.1, fun u hu =>
      (flatFiberCenters_subset_frozen_zero ha hU.isPreconnected hu hz).2⟩
  · rintro ⟨hz, hall⟩
    obtain ⟨u, hu⟩ := hU.nonempty
    refine ⟨hz, u, hu, ?_⟩
    filter_upwards [hoU.mem_nhds hu] with v hv
    exact hall v hv

theorem flatFiberCenters_closure_null_on_compact {d : ℕ}
    {f : Parameters 2 d → ℝ} {V : Set (Base 2)} {U : Set (Aux d)}
    (ho : IsOpen V) (hV : IsPreconnected V) (hU : IsPreconnected U)
    (ha : AnalyticOnNhd ℝ f (V ×ˢ U))
    (hne : ∃ z ∈ V, ∃ u ∈ U, f (z, u) ≠ 0)
    {K : Set (Base 2)} (hK : IsCompact K) (hKV : K ⊆ V) :
    volume (closure (K ∩ flatFiberCenters f V U)) = 0 := by
  obtain ⟨z₀, hz₀, u₀, hu₀, hnonzero⟩ := hne
  have hag : AnalyticOnNhd ℝ (fun z => f (z, u₀)) V := by
    intro z hz
    exact (ha (z, u₀) ⟨hz, hu₀⟩).comp (f := fun z => (z, u₀))
      (analyticAt_id.prod analyticAt_const)
  exact closure_analytic_zeros_null_of_compact_container ho hag hV
    ⟨z₀, hz₀, hnonzero⟩ hK hKV inter_subset_left
    (fun z hz => (flatFiberCenters_subset_frozen_zero ha hU hu₀ hz.2).2)

/-- Every nonempty open product patch in the connected analytic domain
contains an actual nonzero value of a globally nontrivial function. -/
theorem exists_nonzero_on_analytic_product_patch {d : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (ha : AnalyticOnNhd ℝ f W) (hW : IsPreconnected W)
    (hne : ∃ p ∈ W, f p ≠ 0)
    {V : Set (Base 2)} {U : Set (Aux d)}
    (hoV : IsOpen V) (hoU : IsOpen U) (hnV : V.Nonempty) (hnU : U.Nonempty)
    (hVU : V ×ˢ U ⊆ W) :
    ∃ z ∈ V, ∃ u ∈ U, f (z, u) ≠ 0 := by
  by_contra! hall
  obtain ⟨z, hz⟩ := hnV
  obtain ⟨u, hu⟩ := hnU
  have hflat : f =ᶠ[𝓝 (z, u)] 0 := by
    filter_upwards [(hoV.prod hoU).mem_nhds ⟨hz, hu⟩] with p hp
    exact hall p.1 hp.1 p.2 hp.2
  have he := ha.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    hW (hVU ⟨hz, hu⟩) hflat
  obtain ⟨p, hp, hfp⟩ := hne
  exact hfp (he hp)

/-- A closed null envelope is constructed directly from the original
analytic function and product patch; no projected-nullity premise occurs. -/
theorem analytic_product_patch_flat_centers_closed_null {d : ℕ}
    {f : Parameters 2 d → ℝ} {W : Set (Parameters 2 d)}
    (ha : AnalyticOnNhd ℝ f W) (hW : IsPreconnected W)
    (hne : ∃ p ∈ W, f p ≠ 0)
    {V : Set (Base 2)} {U : Set (Aux d)}
    (hoV : IsOpen V) (hoU : IsOpen U) (hV : IsConnected V) (hU : IsConnected U)
    (hVU : V ×ˢ U ⊆ W) {K : Set (Base 2)}
    (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ E : Set (Base 2), IsClosed E ∧ volume E = 0 ∧
      closure (K ∩ flatFiberCenters f V U) ⊆ E := by
  have hnonzero := exists_nonzero_on_analytic_product_patch ha hW hne
    hoV hoU hV.nonempty hU.nonempty hVU
  refine ⟨closure (K ∩ flatFiberCenters f V U), isClosed_closure, ?_, Subset.rfl⟩
  exact flatFiberCenters_closure_null_on_compact hoV hV.isPreconnected hU.isPreconnected
    (ha.mono hVU) hnonzero hK hKV

end PlanarNikodym
