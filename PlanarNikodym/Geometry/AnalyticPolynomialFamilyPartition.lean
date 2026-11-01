import PlanarNikodym.Geometry.AnalyticPolynomialFamilyRootBranches
import PlanarNikodym.Geometry.FiniteFamilyGraphCompatibility

/-! A simultaneous finite analytic sign partition for a polynomial family at a
parameter where its actual collision determinant is nonzero. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

/-- Construct the whole regular finite-family partition, including graph ownership
and simultaneous sign constancy. No root list, separation neighborhood, or sign
compatibility certificate is assumed. The bounded cylinder contains every real root. -/
theorem exists_analytic_polynomial_family_root_partition
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Fintype J]
    (m : J → ℕ) (a : E → ∀ j, Fin (m j) → ℝ) (x₀ : E)
    (ha : ∀ j, AnalyticAt ℝ (fun x => a x j) x₀)
    (hdet : weierstrassFamilyCollisionDet m (a x₀) ≠ 0) :
    ∃ (n : ℕ) (ε R : ℝ), 0 < ε ∧ 0 < R ∧ ∃ ρ : Fin n → E → ℝ,
      (∀ j, AnalyticOnNhd ℝ (fun x => a x j) (Metric.ball x₀ ε)) ∧
      (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x)) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo (-R) R) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ t : ℝ,
        (∃ j, (weierstrassPolynomial (a x j)).eval t = 0) ↔ ∃ i, t = ρ i x) ∧
      let C := analyticCylindricalCell (Metric.ball x₀ ε) (analyticRootCuts (-R) R ρ)
      (⋃ i, C i) = Metric.ball x₀ ε ×ˢ Ioo (-R) R ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ i, IsConnected (C i)) ∧
      (Set.range C).ncard = 2 * n + 1 ∧
      ∀ i j,
        (∀ z ∈ C i, (weierstrassPolynomial (a z.1 j)).eval z.2 < 0) ∨
        (∀ z ∈ C i, (weierstrassPolynomial (a z.1 j)).eval z.2 = 0) ∨
        (∀ z ∈ C i, 0 < (weierstrassPolynomial (a z.1 j)).eval z.2) := by
  obtain ⟨n, ε, R, hε, hR, ρ, hcoef, hdetU, hρ, hmono, hb, hroots⟩ :=
    exists_ordered_analytic_polynomial_family_root_branches m a x₀ ha hdet
  let U := Metric.ball x₀ ε
  let c := analyticRootCuts (-R) R ρ
  have hAB : -R < R := by linarith
  have hU : IsConnected U := Metric.isConnected_ball hε
  have hpart := analytic_ordered_root_partition (-R) R ρ hAB hU hρ hmono hb
  have hcuts := strictMono_analyticRootCuts (-R) R ρ hAB hmono hb
  have hcutsA := analyticOnNhd_analyticRootCuts (-R) R ρ hρ
  have hband : analyticBand U (c 0) (c (Fin.last (n + 1))) = U ×ˢ Ioo (-R) R := by
    simp only [c, analyticRootCuts_zero, analyticRootCuts_last]
    rfl
  have hf : ∀ j, ContinuousOn
      (fun z : E × ℝ => (weierstrassPolynomial (a z.1 j)).eval z.2)
      (analyticBand U (c 0) (c (Fin.last (n + 1)))) := by
    intro j z hz
    rw [hband] at hz
    exact (analyticAt_joint_weierstrassPolynomial_eval (fun x => a x j) z.1 z.2
      (hcoef j z.1 hz.1)).continuousAt.continuousWithinAt
  have hsign := analyticCylindricalCell_separated_family_sign_constant c hU hcutsA hcuts
    (fun j z => (weierstrassPolynomial (a z.1 j)).eval z.2) hf
    (by
      intro j z hz hzero
      rw [hband] at hz
      obtain ⟨i, hi⟩ := (hroots z.1 hz.1 z.2).mp ⟨j, hzero⟩
      exact ⟨i, by simpa only [c, analyticRootCuts_interior] using hi⟩)
    (by
      intro l z hz
      apply (hroots z.1 (mem_analyticCylindricalCell_fst hz) z.2).mpr
      exact ⟨l, by simpa only [c, analyticCylindricalCell, analyticGraph,
        analyticRootCuts_interior] using hz.2⟩)
    (by
      intro z hz i j hi hj
      rw [hband] at hz
      by_contra hij
      exact (simple_disjoint_roots_of_weierstrassFamilyCollisionDet_ne_zero m (a z.1)
        (hdetU z.1 hz.1)).2 i j hij z.2 ⟨hi, hj⟩)
  exact ⟨n, ε, R, hε, hR, ρ, hcoef, hρ, hmono, hb, hroots,
    hpart.1, hpart.2.1, hpart.2.2,
    ncard_range_analyticCylindricalCell _ hU hcutsA hcuts, hsign⟩

end PlanarNikodym
