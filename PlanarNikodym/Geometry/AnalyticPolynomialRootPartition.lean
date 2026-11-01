import PlanarNikodym.Geometry.AnalyticPolynomialRootBranches
import PlanarNikodym.Geometry.AnalyticCylindricalPartition

/-! An actual finite connected sign-invariant cylindrical partition near a regular
monic polynomial parameter. All real roots are accounted for by the constructed graphs. -/

noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The regular monic-polynomial terminal step: construct all real root graphs and the
`2n+1` actual distinct connected cells between fixed outer boundaries. Every cell has
one constant sign (or is identically zero) for the original polynomial evaluation.
The sole regularity condition is nonvanishing of the actual collision determinant. -/
theorem exists_analytic_polynomial_root_partition
    {m : ℕ} (a : E → Fin m → ℝ) (x₀ : E) (ha : AnalyticAt ℝ a x₀)
    (hdet : weierstrassCollisionDet (a x₀) ≠ 0) :
    ∃ (n : ℕ) (ε R : ℝ), 0 < ε ∧ 0 < R ∧ ∃ ρ : Fin n → E → ℝ,
      AnalyticOnNhd ℝ a (Metric.ball x₀ ε) ∧
      (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x)) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo (-R) R) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ t : ℝ,
        (weierstrassPolynomial (a x)).eval t = 0 ↔ ∃ i, t = ρ i x) ∧
      let C := analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts (-R) R ρ)
      (⋃ i, C i) = Metric.ball x₀ ε ×ˢ Ioo (-R) R ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ i, IsConnected (C i)) ∧
      (Set.range C).ncard = 2 * n + 1 ∧
      ∀ i,
        (∀ z ∈ C i, (weierstrassPolynomial (a z.1)).eval z.2 < 0) ∨
        (∀ z ∈ C i, (weierstrassPolynomial (a z.1)).eval z.2 = 0) ∨
        (∀ z ∈ C i, 0 < (weierstrassPolynomial (a z.1)).eval z.2) := by
  obtain ⟨n, ε, R, hε, hR, ρ, hcoef, hρ, hmono, hb, hroots⟩ :=
    exists_ordered_analytic_polynomial_root_branches_of_collisionDet_ne_zero a x₀ ha hdet
  have hAB : -R < R := by linarith
  have hU : IsConnected (Metric.ball x₀ ε) := Metric.isConnected_ball hε
  have hpart := analytic_ordered_root_partition (-R) R ρ hAB hU hρ hmono hb
  have hcuts := strictMono_analyticRootCuts (-R) R ρ hAB hmono hb
  have hcutsA := analyticOnNhd_analyticRootCuts (-R) R ρ hρ
  have hf : ContinuousOn
      (fun z : E × ℝ => (weierstrassPolynomial (a z.1)).eval z.2)
      (Metric.ball x₀ ε ×ˢ Ioo (-R) R) := by
    intro z hz
    exact (analyticAt_joint_weierstrassPolynomial_eval a z.1 z.2
      (hcoef z.1 hz.1)).continuousAt.continuousWithinAt
  have hsign := analytic_ordered_root_sign_partition (-R) R ρ hAB hU hρ hmono hb
    (fun z : E × ℝ => (weierstrassPolynomial (a z.1)).eval z.2) hf
    (fun x hx t _ => hroots x hx t)
  refine ⟨n, ε, R, hε, hR, ρ, hcoef, hρ, hmono, hb, hroots,
    hpart.1, hpart.2.1, hpart.2.2, ?_, ?_⟩
  · exact ncard_range_analyticCylindricalCell _ hU hcutsA hcuts
  · intro i
    cases i with
    | inl i => exact Or.inr (Or.inl (hsign.1 i))
    | inr i =>
      rcases hsign.2 i with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

end PlanarNikodym
