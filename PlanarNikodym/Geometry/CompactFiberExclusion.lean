import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! Joint continuity excludes new zeros uniformly over an actual compact fiber.
The parameter neighborhood is constructed before quantifying the entire fiber. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

/-- A compact collection of nonzero fiber values remains nonzero on one common
open parameter neighborhood. The compact set is allowed to be empty. -/
theorem exists_open_nhds_compact_fiber_nonzero
    {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    (f : E × T → ℝ) (x₀ : E) (K : Set T) (hK : IsCompact K)
    (hf : ∀ t ∈ K, ContinuousAt f (x₀, t))
    (hn : ∀ t ∈ K, f (x₀, t) ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      ∀ x ∈ U, ∀ t ∈ K, f (x, t) ≠ 0 := by
  classical
  have hprod (t : K) : ∃ (U : Set E) (V : Set T),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen V ∧ t.val ∈ V ∧
      U ×ˢ V ⊆ {z | f z ≠ 0} :=
    mem_nhds_prod_iff'.mp ((hf t t.property).eventually_ne (hn t t.property))
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
