import PlanarNikodym.Geometry.AnalyticNonflatDirections
import Mathlib.Analysis.Analytic.Order

/-! Actual finite one-variable orders in one common nonzero direction for an
arbitrary finite analytic family, including members whose germ is zero. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nonflat real analytic germs have a first finite nonzero derivative. -/
theorem exists_finite_analytic_line_order {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0)
    (hn : ¬ ∀ᶠ t in 𝓝 0, g t = 0) :
    ∃ m : ℕ, (∀ k < m, iteratedDeriv k g 0 = 0) ∧ iteratedDeriv m g 0 ≠ 0 := by
  have ho : analyticOrderAt g 0 ≠ ⊤ := fun h => hn (analyticOrderAt_eq_top.mp h)
  exact ⟨analyticOrderNatAt g 0,
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mp (Nat.cast_analyticOrderNatAt ho).symm⟩

/-- A single actual nonzero direction simultaneously gives either a zero germ
in the original space or a finite first nonzero line derivative for each member. -/
theorem exists_common_finite_analytic_line_orders [Nontrivial E]
    {J : Type*} [Fintype J] (f : J → E → ℝ) (x : E)
    (ha : ∀ j, AnalyticAt ℝ (f j) x) :
    ∃ v : E, v ≠ 0 ∧ ∀ j,
      (∀ᶠ y in 𝓝 x, f j y = 0) ∨
        ∃ m : ℕ,
          (∀ k < m, iteratedDeriv k (fun t : ℝ => f j (x + t • v)) 0 = 0) ∧
          iteratedDeriv m (fun t : ℝ => f j (x + t • v)) 0 ≠ 0 := by
  classical
  let K := {j : J // ¬ ∀ᶠ y in 𝓝 x, f j y = 0}
  obtain ⟨v, hv, hline⟩ := exists_common_nonflat_analytic_direction
    (fun j : K => f j) x (fun j => ha j) (fun j => j.property)
  refine ⟨v, hv, ?_⟩
  intro j
  by_cases hj : ∀ᶠ y in 𝓝 x, f j y = 0
  · exact Or.inl hj
  · exact Or.inr (exists_finite_analytic_line_order (hline ⟨j, hj⟩).1 (hline ⟨j, hj⟩).2)

end PlanarNikodym
