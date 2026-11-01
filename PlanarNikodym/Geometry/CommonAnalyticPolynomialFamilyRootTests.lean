import PlanarNikodym.Geometry.CommonAnalyticPolynomialRootTests
import PlanarNikodym.Geometry.AnalyticPolynomialFamilyRootStrata

/-! One common finite analytic family prepares all the real roots of a
finite family of monic polynomials on connected sign-invariant base subsets. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_common_analytic_polynomial_family_root_tests
    {ι : Type} [Fintype ι] (m : ι → ℕ) (a : (j : ι) → E → Fin (m j) → ℝ)
    (U : Set E) (hU : IsOpen U) (ha : ∀ j, AnalyticOnNhd ℝ (a j) U) :
    ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
      (∀ k, AnalyticOnNhd ℝ (g k) U) ∧
      ∀ C : Set E, C ⊆ U → IsConnected C →
        (∀ k x, x ∈ C → ∀ y, y ∈ C → oneDimensionalSign (g k x) = oneDimensionalSign (g k y)) →
        ∀ j, ∃ (n : ℕ) (Ω : Set E) (ρ : Fin n → E → ℝ),
          n ≤ m j ∧ IsOpen Ω ∧ C ⊆ Ω ∧ Ω ⊆ U ∧
          (∀ i, AnalyticOnNhd ℝ (ρ i) Ω) ∧
          (∀ x ∈ Ω, StrictMono (fun i => ρ i x)) ∧
          ∀ x ∈ C, ∀ t : ℝ, (weierstrassPolynomial (a j x)).eval t = 0 ↔ ∃ i, t = ρ i x := by
  classical
  choose κ hκ g hg hp using fun j => exists_common_analytic_polynomial_root_tests (a j) U hU (ha j)
  letI (j : ι) : Fintype (κ j) := hκ j
  refine ⟨(Σ j, κ j), inferInstance, fun k => g k.1 k.2, fun k => hg k.1 k.2, ?_⟩
  intro C hCU hC hs j
  exact hp j C hCU hC (fun k x hx y hy => hs ⟨j, k⟩ x hx y hy)

end PlanarNikodym
