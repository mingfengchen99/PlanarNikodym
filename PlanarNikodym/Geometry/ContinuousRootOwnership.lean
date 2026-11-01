import PlanarNikodym.Geometry.ContinuousFiniteGraphSelection
import Mathlib.Data.Finset.Image

/-! Continuous lists of member roots have fixed ownership among a complete
list of distinct union roots on a connected base, including repeated roots
and roots shared by different members. -/
noncomputable section
open Set
namespace PlanarNikodym
variable {E : Type*} [TopologicalSpace E]

theorem exists_fixed_continuous_root_indices {n k : ℕ}
    (C : Set E) (hC : IsConnected C) (r : Fin n → E → ℝ) (μ : Fin k → E → ℝ)
    (hr : ∀ i, ContinuousOn (r i) C) (hμ : ∀ j, ContinuousOn (μ j) C)
    (hi : ∀ x ∈ C, Function.Injective (fun i => r i x))
    (hsub : ∀ j x, x ∈ C → ∃ i, μ j x = r i x) :
    ∃ σ : Fin k → Fin n, ∀ j x, x ∈ C → μ j x = r (σ j) x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hC.nonempty
  choose σ hσ using fun j => hsub j x₀ hx₀
  exact ⟨σ, fun j => continuous_selector_eq_on_preconnected C hC.isPreconnected r (μ j)
    hr (hμ j) hi (hsub j) hx₀ (σ j) (hσ j)⟩

/-- The member root set occupies one fixed finite subset of the union-root
indices; the construction does not assume disjoint member zero sets. -/
theorem exists_fixed_continuous_root_ownership {n k : ℕ}
    (C : Set E) (hC : IsConnected C) (r : Fin n → E → ℝ) (μ : Fin k → E → ℝ)
    (hr : ∀ i, ContinuousOn (r i) C) (hμ : ∀ j, ContinuousOn (μ j) C)
    (hi : ∀ x ∈ C, Function.Injective (fun i => r i x))
    (hsub : ∀ j x, x ∈ C → ∃ i, μ j x = r i x) :
    ∃ S : Finset (Fin n), ∀ x ∈ C, ∀ i, (∃ j, r i x = μ j x) ↔ i ∈ S := by
  classical
  obtain ⟨σ, hσ⟩ := exists_fixed_continuous_root_indices C hC r μ hr hμ hi hsub
  refine ⟨Finset.univ.image σ, ?_⟩
  intro x hx i
  constructor
  · rintro ⟨j, hj⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hi x hx ((hσ j x hx).symm.trans hj.symm)⟩
  · intro hiS
    obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hiS
    exact ⟨j, hji ▸ (hσ j x hx).symm⟩

end PlanarNikodym
