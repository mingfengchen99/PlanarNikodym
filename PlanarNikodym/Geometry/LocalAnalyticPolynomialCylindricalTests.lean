import PlanarNikodym.Geometry.CommonAnalyticPolynomialCylindricalTests
import PlanarNikodym.Geometry.WeierstrassRootBounds

/-! A genuine local all-parameter polynomial lifting theorem from only the
original finite family of analytic coefficient germs. The common domain,
root bound and finite analytic tests are all constructed. -/
noncomputable section
open Set Filter Polynomial Metric
open scoped Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local simultaneous root preparation and connected sign-invariant lifting,
including every collision parameter, from the original analytic germs. -/
theorem exists_local_analytic_polynomial_cylindrical_tests
    {J : Type} [Fintype J] (m : J → ℕ) (a : (j : J) → E → Fin (m j) → ℝ)
    (x₀ : E) (ha : ∀ j, AnalyticAt ℝ (a j) x₀) :
    ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      (∀ j, AnalyticOnNhd ℝ (a j) (closedBall x₀ ε)) ∧
      HasAnalyticPolynomialCylindricalTests m a (ball x₀ ε) R := by
  let A := weierstrassFamilyProductCoefficients m (fun y j => a j y)
  have hA : AnalyticAt ℝ A x₀ := analyticAt_weierstrassFamilyProductCoefficients m _ x₀ ha
  obtain ⟨W, R, hW, hxW, hR, hbound⟩ :=
    exists_open_nhds_uniform_weierstrass_root_bound A x₀ hA.continuousAt
  have hnear : {x | x ∈ W ∧ ∀ j, AnalyticAt ℝ (a j) x} ∈ 𝓝 x₀ := by
    exact inter_mem (hW.mem_nhds hxW)
      (Filter.eventually_all.mpr (fun j => (ha j).eventually_analyticAt))
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcl : closedBall x₀ ε ⊆ ball x₀ δ := by
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    dsimp [ε] at hx
    linarith
  have han (j : J) : AnalyticOnNhd ℝ (a j) (closedBall x₀ ε) :=
    fun x hx => (hb (hcl hx)).2 j
  refine ⟨ε, R, hε, hR, han, ?_⟩
  exact exists_common_analytic_polynomial_cylindrical_tests m a (ball x₀ ε) isOpen_ball
    (fun j => (han j).mono ball_subset_closedBall) R hR
    (fun x hx t ht => hbound x (hb (hcl (ball_subset_closedBall hx))).1 t ht)

end PlanarNikodym
