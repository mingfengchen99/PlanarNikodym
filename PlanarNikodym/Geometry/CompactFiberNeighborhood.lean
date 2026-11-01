import PlanarNikodym.Geometry.CompactFiberExclusion

/-! A neighborhood property along a compact fiber holds on one common base neighborhood. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

theorem exists_open_nhds_compact_fiber_property
    {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    (P : E × T → Prop) (x₀ : E) (K : Set T) (hK : IsCompact K)
    (hP : ∀ t ∈ K, ∀ᶠ z in 𝓝 (x₀, t), P z) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      ∀ x ∈ U, ∀ t ∈ K, P (x, t) := by
  classical
  have hprod (t : K) : ∃ (U : Set E) (V : Set T),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t.val ∈ V ∧
      U ×ˢ V ⊆ {z | P z} :=
    mem_nhds_prod_iff'.mp (hP t t.property)
  choose U V hU hxU hV htV hUV using hprod
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover V hV (by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, htV ⟨t, ht⟩⟩)
  refine ⟨⋂ t ∈ S, U t, isOpen_biInter_finset fun t _ => hU t, ?_, ?_⟩
  · exact mem_iInter.mpr fun t => mem_iInter.mpr fun _ => hxU t
  · intro x hx t ht
    obtain ⟨y, hy, hty⟩ := mem_iUnion₂.mp (hS ht)
    exact hUV y ⟨mem_iInter.mp (mem_iInter.mp hx y) hy, hty⟩

end PlanarNikodym
