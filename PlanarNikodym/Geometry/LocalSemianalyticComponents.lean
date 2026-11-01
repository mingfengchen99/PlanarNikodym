import PlanarNikodym.Geometry.FiniteConnectedSignComponents
import Mathlib.Topology.LocallyFinite

/-! Local semianalyticity means a genuine local finite Boolean combination
of signs of analytic functions. The proved finite analytic refinement gives
local finiteness of actual components. No general R_an quantifier elimination
or component definability is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

/-- The usual local analytic-sign description of a semianalytic set. -/
def LocallySemianalytic {d : ℕ} (A : Set (Fin d → ℝ)) : Prop :=
  ∀ x, ∃ O : Set (Fin d → ℝ), IsOpen O ∧ x ∈ O ∧
    ∃ (J : Type) (_ : Fintype J) (f : J → (Fin d → ℝ) → ℝ),
      (∀ j, AnalyticOnNhd ℝ (f j) O) ∧ ∃ Q : (J → Fin 3) → Prop,
        ∀ y ∈ O, y ∈ A ↔ Q (fun j => oneDimensionalSign (f j y))

theorem LocallySemianalytic.exists_local_connected_sign_cover
    {d : ℕ} {A : Set (Fin d → ℝ)} (hA : LocallySemianalytic A) (x : Fin d → ℝ) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ x ∈ U ∧
      ∃ (κ : Type) (_ : Fintype κ) (g : κ → (Fin d → ℝ) → ℝ)
        (S : Set (κ → Fin 3)),
        (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
        (∀ s ∈ S, IsConnected (analyticStrongSignCell U g s)) ∧
        A ∩ U = ⋃ s : S, analyticStrongSignCell U g s := by
  obtain ⟨O, hO, hxO, J, hJ, f, hf, Q, hrep⟩ := hA x
  obtain ⟨U, hU, hxU, hUO, κ, hκ, g, S, hg, hconn, he⟩ :=
    exists_local_finite_analytic_sign_component_cover f x (fun j => hf j x hxO) O hO hxO Q
  refine ⟨U, hU, hxU, κ, hκ, g, S, hg, hconn, ?_⟩
  rw [← he]
  ext y
  exact ⟨fun hy => ⟨hy.2, (hrep y (hUO hy.2)).mp hy.1⟩,
    fun hy => ⟨(hrep y (hUO hy.1)).mpr hy.2, hy.1⟩⟩

/-- The actual global components meet each sufficiently small neighborhood
in only finitely many different components, including at boundary points. -/
theorem LocallySemianalytic.locallyFinite_components
    {d : ℕ} {A : Set (Fin d → ℝ)} (hA : LocallySemianalytic A) :
    LocallyFinite (fun C : componentDomains A => C.val) := by
  classical
  intro x
  obtain ⟨U, hU, hxU, κ, hκ, g, S, _hg, hconn, he⟩ := hA.exists_local_connected_sign_cover x
  let D (s : S) := analyticStrongSignCell U g s
  have hsub (s : S) : D s ⊆ A := by
    intro y hy
    have h : y ∈ A ∩ U := by rw [he]; exact mem_iUnion.mpr ⟨s, hy⟩
    exact h.1
  choose u hu using fun s : S => (hconn s s.2).nonempty
  let F (s : S) : componentDomains A :=
    ⟨connectedComponentIn A (u s), u s, hsub s (hu s), rfl⟩
  refine ⟨U, hU.mem_nhds hxU, (Set.finite_range F).subset ?_⟩
  intro C hCU
  obtain ⟨y, hyC, hyU⟩ := hCU
  obtain ⟨z, hzA, hzC⟩ := C.property
  have hyA : y ∈ A := by
    apply connectedComponentIn_subset A z
    rwa [← hzC]
  have hycov : y ∈ ⋃ s : S, D s := by rw [← he]; exact ⟨hyA, hyU⟩
  obtain ⟨s, hs⟩ := mem_iUnion.mp hycov
  refine ⟨s, Subtype.ext ?_⟩
  have hy1 : connectedComponentIn A (u s) = connectedComponentIn A y :=
    connectedComponentIn_eq ((hconn s s.2).isPreconnected.subset_connectedComponentIn
      (hu s) (hsub s) hs)
  have hy2 : connectedComponentIn A z = connectedComponentIn A y :=
    connectedComponentIn_eq (hzC ▸ hyC)
  exact hy1.trans (hy2.symm.trans hzC.symm)

end PlanarNikodym
