import PlanarNikodym.Geometry.LocalSemianalyticComponents
import Mathlib.Topology.Compactness.LocallyFinite

/-! Every actual component and every union of actual components of a
semianalytic set is semianalytic. The local finite analytic sign cover is
used directly to construct the Boolean sign description. Compact containers
also give actual finite global component families. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem preconnected_subset_componentDomain_of_inter
    {X : Type*} [TopologicalSpace X] {A D C : Set X}
    (hD : IsPreconnected D) (hDA : D ⊆ A) (hC : C ∈ componentDomains A)
    (hne : (D ∩ C).Nonempty) : D ⊆ C := by
  obtain ⟨z, hzD, hzC⟩ := hne
  obtain ⟨x, _, hCx⟩ := hC
  have hzComp : z ∈ connectedComponentIn A x := hCx ▸ hzC
  have he := connectedComponentIn_eq hzComp
  rw [hCx, he]
  exact hD.subset_connectedComponentIn hzD hDA

theorem LocallySemianalytic.sUnion_components
    {d : ℕ} {A : Set (Fin d → ℝ)} (hA : LocallySemianalytic A)
    (B : Set (Set (Fin d → ℝ))) (hBA : B ⊆ componentDomains A) :
    LocallySemianalytic (⋃₀ B) := by
  classical
  have hUnionA : ⋃₀ B ⊆ A := by
    intro y hy
    obtain ⟨C, hCB, hyC⟩ := mem_sUnion.mp hy
    obtain ⟨x, _, hCx⟩ := hBA hCB
    exact connectedComponentIn_subset A x (hCx ▸ hyC)
  intro x
  obtain ⟨U, hU, hxU, κ, hκ, g, S, hg, hconn, hcover⟩ :=
    hA.exists_local_connected_sign_cover x
  let D (s : κ → Fin 3) := analyticStrongSignCell U g s
  have hDA (s : κ → Fin 3) (hs : s ∈ S) : D s ⊆ A := by
    intro y hy
    have h : y ∈ A ∩ U := by
      rw [hcover]
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, hy⟩
    exact h.1
  let Q : (κ → Fin 3) → Prop := fun s => s ∈ S ∧ (D s ∩ ⋃₀ B).Nonempty
  refine ⟨U, hU, hxU, κ, hκ, g, hg, Q, ?_⟩
  intro y hyU
  let t : κ → Fin 3 := fun k => oneDimensionalSign (g k y)
  have hyt : y ∈ D t := ⟨hyU, fun _ => rfl⟩
  constructor
  · intro hyB
    have hycover : y ∈ ⋃ s : S, D s := by
      rw [← hcover]
      exact ⟨hUnionA hyB, hyU⟩
    obtain ⟨s, hys⟩ := mem_iUnion.mp hycover
    have he : s.val = t := funext (fun k => (hys.2 k).symm)
    have htS : t ∈ S := by rw [← he]; exact s.property
    exact ⟨htS, y, hyt, hyB⟩
  · rintro ⟨htS, z, hzD, hzB⟩
    obtain ⟨C, hCB, hzC⟩ := mem_sUnion.mp hzB
    have hDC : D t ⊆ C := preconnected_subset_componentDomain_of_inter
      (hconn t htS).isPreconnected (hDA t htS) (hBA hCB) ⟨z, hzD, hzC⟩
    exact mem_sUnion.mpr ⟨C, hCB, hDC hyt⟩

theorem LocallySemianalytic.componentDomain
    {d : ℕ} {A C : Set (Fin d → ℝ)} (hA : LocallySemianalytic A)
    (hC : C ∈ componentDomains A) : LocallySemianalytic C := by
  simpa only [sUnion_singleton] using
    hA.sUnion_components {C} (singleton_subset_iff.mpr hC)

theorem LocallySemianalytic.connectedComponentIn
    {d : ℕ} {A : Set (Fin d → ℝ)} (hA : LocallySemianalytic A) (x : Fin d → ℝ) :
    LocallySemianalytic (connectedComponentIn A x) := by
  by_cases hx : x ∈ A
  · exact hA.componentDomain ⟨x, hx, rfl⟩
  · rw [connectedComponentIn_eq_empty hx]
    simpa only [sUnion_empty] using hA.sUnion_components ∅ (empty_subset _)

theorem LocallySemianalytic.components_finite_of_subset_compact
    {d : ℕ} {A K : Set (Fin d → ℝ)} (hA : LocallySemianalytic A)
    (hK : IsCompact K) (hAK : A ⊆ K) : (componentDomains A).Finite := by
  classical
  have hf := hA.locallyFinite_components.finite_nonempty_inter_compact hK
  have hall : (univ : Set (componentDomains A)).Finite := hf.subset (by
    intro C _
    obtain ⟨x, hxA, hCx⟩ := C.property
    refine ⟨x, ?_, hAK hxA⟩
    rw [hCx]
    exact mem_connectedComponentIn hxA)
  apply (hall.image (fun C : componentDomains A => C.val)).subset
  intro C hC
  exact ⟨⟨C, hC⟩, mem_univ _, rfl⟩

theorem LocallySemianalytic.components_finite_of_compact_closure
    {d : ℕ} {A : Set (Fin d → ℝ)} (hA : LocallySemianalytic A)
    (hcompact : IsCompact (closure A)) : (componentDomains A).Finite :=
  hA.components_finite_of_subset_compact hcompact subset_closure

theorem LocallySemianalytic.components_finite_of_bounded
    {d : ℕ} {A : Set (Fin d → ℝ)} (hA : LocallySemianalytic A)
    (hbounded : Bornology.IsBounded A) : (componentDomains A).Finite :=
  hA.components_finite_of_compact_closure hbounded.isCompact_closure

end PlanarNikodym
