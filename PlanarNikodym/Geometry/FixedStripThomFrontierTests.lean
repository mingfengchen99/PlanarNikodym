import PlanarNikodym.Geometry.FixedStripDerivativeThomTests
import PlanarNikodym.Geometry.ThomAnalyticDerivativeClosure

/-! Common analytic tests construct both connected fixed-strip Thom cells
and their exact relative weak-sign closures, including collision parameters.
The required nonempty fiber property is proved by the root/band lifting. -/
noncomputable section
open Set Filter Metric Polynomial
open scoped Topology
namespace PlanarNikodym
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_fixedStrip_thom_frontier_tests
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (x₀ : E) (ha : ∀ j, AnalyticAt ℝ (a j) x₀) (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (κ : Type) (_ : Fintype κ) (g : κ → E → ℝ),
      (∀ j, AnalyticOnNhd ℝ (a j) (ball x₀ ε)) ∧
      (∀ k, AnalyticOnNhd ℝ (g k) (ball x₀ ε)) ∧
      ∀ C : Set E, C ⊆ ball x₀ ε → IsConnected C →
        (∀ k x, x ∈ C → ∀ y, y ∈ C → oneDimensionalSign (g k x) = oneDimensionalSign (g k y)) →
        ∀ s : PolynomialDerivativeIndex (stripPolynomialDegree m) → Fin 3,
          let P := fun x => polynomialDerivativeFamily (fun j => weierstrassPolynomial
            (stripPolynomialCoefficients m a r j x)) (stripPolynomialDegree m)
          polynomialCylindricalSignCell C (-r) r P s = ∅ ∨
          (IsConnected (polynomialCylindricalSignCell C (-r) r P s) ∧
            closure (polynomialCylindricalSignCell C (-r) r P s) ∩
              (ball x₀ ε ×ˢ Ioo (-r) r) =
            {z | z.1 ∈ closure C ∩ ball x₀ ε ∧ z.2 ∈ Ioo (-r) r ∧
              z.2 ∈ polynomialThomFamilyCell true (P z.1) s}) := by
  classical
  obtain ⟨δ, hδ, κ, hκ, g, hg, hlift⟩ :=
    exists_fixedStrip_analytic_derivative_thom_tests m a x₀ ha r hr
  have hnear : {x : E | ∀ j, AnalyticAt ℝ (a j) x} ∈ 𝓝 x₀ :=
    Filter.eventually_all.mpr (fun j => (ha j).eventually_analyticAt)
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := min δ η
  have hε : 0 < ε := lt_min hδ hη
  have hεδ : ball x₀ ε ⊆ ball x₀ δ := ball_subset_ball (min_le_left _ _)
  have hεη : ball x₀ ε ⊆ ball x₀ η := ball_subset_ball (min_le_right _ _)
  have haU (j : J) : AnalyticOnNhd ℝ (a j) (ball x₀ ε) :=
    fun _ hx => hηsub (hεη hx) j
  have hA (j : J ⊕ Fin 2) :
      AnalyticOnNhd ℝ (stripPolynomialCoefficients m a r j) (ball x₀ ε) := by
    rcases j with j | i
    · exact haU j
    · exact fun _ _ => analyticAt_const
  refine ⟨ε, hε, κ, hκ, g, haU, fun k => (hg k).mono hεδ, ?_⟩
  intro C hCU hC hs s
  dsimp only
  rcases hlift C (hCU.trans hεδ) hC hs s with he | ⟨hc, hfiber⟩
  · exact Or.inl he
  · refine Or.inr ⟨hc, ?_⟩
    apply analyticDerivativeCylindricalSignCell_closure C (ball x₀ ε)
      (stripPolynomialDegree m) (stripPolynomialCoefficients m a r)
      isOpen_ball hCU hA (-r) r s
    intro x hx
    obtain ⟨t, ht⟩ := hfiber x hx
    exact ⟨t, ht.2⟩

end PlanarNikodym
