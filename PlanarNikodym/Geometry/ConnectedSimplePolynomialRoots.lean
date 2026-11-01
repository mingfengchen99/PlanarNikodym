import PlanarNikodym.Geometry.AnalyticGlobalPolynomialRoots
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Real-root count is constant on every preconnected subset of a simple-root
ambient domain. No openness or smoothness of that subset is required. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuousOn_polynomialRealRootCount_of_simple
    {m : ℕ} (a : E → Fin m → ℝ) (V C : Set E)
    (hV : IsOpen V) (ha : AnalyticOnNhd ℝ a V) (hCV : C ⊆ V)
    (hΔ : ∀ x ∈ C, weierstrassCollisionDet (a x) ≠ 0) :
    ContinuousOn (fun x => polynomialRealRootCount (a x)) C := by
  intro x hx
  have hxD : x ∈ polynomialSimpleRootCountDomain a V (polynomialRealRootCount (a x)) :=
    ⟨hCV hx, hΔ x hx, rfl⟩
  have hD := (isOpen_polynomialSimpleRootCountDomain a V hV ha _).mem_nhds hxD
  apply continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
  filter_upwards [nhdsWithin_le_nhds hD] with y hy
  exact hy.2.2

theorem polynomialRealRootCount_eq_on_preconnected
    {m : ℕ} (a : E → Fin m → ℝ) (V C : Set E)
    (hV : IsOpen V) (ha : AnalyticOnNhd ℝ a V) (hCV : C ⊆ V)
    (hC : IsPreconnected C) (hΔ : ∀ x ∈ C, weierstrassCollisionDet (a x) ≠ 0)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    polynomialRealRootCount (a x) = polynomialRealRootCount (a y) :=
  hC.constant (continuousOn_polynomialRealRootCount_of_simple a V C hV ha hCV hΔ) hx hy

/-- A connected subset of an analytic simple-root ambient has one complete,
strictly ordered root list, analytic on an actual open neighborhood of the
entire subset. The subset need not itself be open. -/
theorem exists_ordered_analytic_polynomial_roots_on_connected_subset
    {m : ℕ} (a : E → Fin m → ℝ) (V C : Set E)
    (hV : IsOpen V) (ha : AnalyticOnNhd ℝ a V) (hCV : C ⊆ V)
    (hC : IsConnected C) (hΔ : ∀ x ∈ C, weierstrassCollisionDet (a x) ≠ 0) :
    ∃ (n : ℕ) (Ω : Set E) (ρ : Fin n → E → ℝ),
      n ≤ m ∧ IsOpen Ω ∧ C ⊆ Ω ∧ Ω ⊆ V ∧
      (∀ i, AnalyticOnNhd ℝ (ρ i) Ω) ∧
      (∀ x ∈ Ω, StrictMono (fun i => ρ i x)) ∧
      ∀ x ∈ Ω, ∀ t : ℝ, (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = ρ i x := by
  obtain ⟨x₀, hx₀⟩ := hC.nonempty
  let n := polynomialRealRootCount (a x₀)
  let Ω := polynomialSimpleRootCountDomain a V n
  obtain ⟨ho, ρ, hρ, hm, hr⟩ := exists_global_ordered_analytic_polynomial_roots a V hV ha n
  refine ⟨n, Ω, ρ, polynomialRealRootCount_le _, ho, ?_, fun _ hx => hx.1, hρ, hm, hr⟩
  intro x hx
  exact ⟨hCV hx, hΔ x hx,
    polynomialRealRootCount_eq_on_preconnected a V C hV ha hCV hC.isPreconnected hΔ hx hx₀⟩

end PlanarNikodym
