import PlanarNikodym.Geometry.AnalyticPolynomialRootBranches
import PlanarNikodym.Geometry.AnalyticFamilyDiscriminant
import PlanarNikodym.Geometry.FiniteProductSimpleRoots

/-! Complete ordered analytic branches of the zero union of a finite polynomial
family, on the nonzero locus of its actual collision determinant. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Fintype J]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The radius controls every member and every real root on one common open base set. -/
theorem exists_open_nhds_uniform_weierstrass_family_root_bound
    (m : J → ℕ) (a : E → ∀ j, Fin (m j) → ℝ) (x₀ : E)
    (ha : ∀ j, ContinuousAt (fun x => a x j) x₀) :
    ∃ (U : Set E) (R : ℝ), IsOpen U ∧ x₀ ∈ U ∧ 0 < R ∧
      ∀ x ∈ U, ∀ j t, (weierstrassPolynomial (a x j)).eval t = 0 → |t| < R := by
  classical
  have h (j : J) := exists_open_nhds_uniform_weierstrass_root_bound
    (fun x => a x j) x₀ (ha j)
  choose U R hU hxU hR hb using h
  refine ⟨⋂ j, U j, 1 + ∑ j, R j, isOpen_iInter_of_finite hU,
    mem_iInter.mpr hxU, ?_, ?_⟩
  · have : 0 ≤ ∑ j, R j := Finset.sum_nonneg fun j _ => (hR j).le
    linarith
  · intro x hx j t ht
    have hsmall := hb j x (mem_iInter.mp hx j) t ht
    have hle : R j ≤ ∑ k, R k :=
      Finset.single_le_sum (fun k _ => (hR k).le) (Finset.mem_univ j)
    linarith

/-- The actual family determinant selects a neighborhood where all real roots of
all members are exhausted by one finite ordered analytic family. -/
theorem exists_ordered_analytic_polynomial_family_root_branches
    (m : J → ℕ) (a : E → ∀ j, Fin (m j) → ℝ) (x₀ : E)
    (ha : ∀ j, AnalyticAt ℝ (fun x => a x j) x₀)
    (hdet : weierstrassFamilyCollisionDet m (a x₀) ≠ 0) :
    ∃ (n : ℕ) (ε R : ℝ), 0 < ε ∧ 0 < R ∧ ∃ ρ : Fin n → E → ℝ,
      (∀ j, AnalyticOnNhd ℝ (fun x => a x j) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, weierstrassFamilyCollisionDet m (a x) ≠ 0) ∧
      (∀ i, AnalyticOnNhd ℝ (ρ i) (Metric.ball x₀ ε)) ∧
      (∀ x ∈ Metric.ball x₀ ε, StrictMono (fun i => ρ i x)) ∧
      (∀ x ∈ Metric.ball x₀ ε, ∀ i, ρ i x ∈ Ioo (-R) R) ∧
      ∀ x ∈ Metric.ball x₀ ε, ∀ t : ℝ,
        (∃ j, (weierstrassPolynomial (a x j)).eval t = 0) ↔ ∃ i, t = ρ i x := by
  classical
  obtain ⟨W, R, hW, hxW, hR, hbound⟩ :=
    exists_open_nhds_uniform_weierstrass_family_root_bound m a x₀
      (fun j => (ha j).continuousAt)
  let f : E × ℝ → ℝ := fun z => ∏ j, (weierstrassPolynomial (a z.1 j)).eval z.2
  have hz (x : E) (t : ℝ) : f (x, t) = 0 ↔
      ∃ j, (weierstrassPolynomial (a x j)).eval t = 0 := by
    simp only [f, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  have hleft : f (x₀, -R) ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := (hz x₀ (-R)).mp h
    have h := hbound x₀ hxW j (-R) hj
    simp [abs_neg, abs_of_pos hR] at h
  have hright : f (x₀, R) ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := (hz x₀ R).mp h
    have h := hbound x₀ hxW j R hj
    simp [abs_of_pos hR] at h
  obtain ⟨n, ε₀, hε₀, ρ, hρ, hmono, hI, hroots⟩ :=
    exists_ordered_analytic_simple_root_branches f x₀ (-R) R (by linarith)
      (fun t _ => analyticAt_joint_weierstrassFamilyProduct m a x₀ t ha)
      hleft hright (fun t _ ht =>
        deriv_weierstrassFamilyProduct_ne_zero_of_collisionDet_ne_zero m (a x₀) hdet t ht)
  have hdetNear := (analyticAt_weierstrassFamilyCollisionDet m a x₀ ha).continuousAt.eventually_ne hdet
  have haNear : ∀ᶠ x in 𝓝 x₀, ∀ j, AnalyticAt ℝ (fun y => a y j) x :=
    eventually_all.mpr (fun j => (ha j).eventually_analyticAt)
  have hnear : {x | x ∈ W ∧ x ∈ Metric.ball x₀ ε₀ ∧
      (∀ j, AnalyticAt ℝ (fun y => a y j) x) ∧
      weierstrassFamilyCollisionDet m (a x) ≠ 0} ∈ 𝓝 x₀ := by
    filter_upwards [hW.mem_nhds hxW, Metric.ball_mem_nhds x₀ hε₀,
      haNear, hdetNear] with x hxW hxB hxa hxd
    exact ⟨hxW, hxB, hxa, hxd⟩
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨n, ε, R, hε, hR, ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    exact (hb hx).2.2.1 j
  · intro x hx
    exact (hb hx).2.2.2
  · intro i x hx
    exact hρ i x (hb hx).2.1
  · intro x hx
    exact hmono x (hb hx).2.1
  · intro x hx i
    exact hI x (hb hx).2.1 i
  · intro x hx t
    constructor
    · rintro ⟨j, hj⟩
      have htI : t ∈ Ioo (-R) R := abs_lt.mp (hbound x (hb hx).1 j t hj)
      exact (hroots x (hb hx).2.1 t htI).mp ((hz x t).mpr ⟨j, hj⟩)
    · rintro ⟨i, rfl⟩
      exact (hz x (ρ i x)).mp ((hroots x (hb hx).2.1 (ρ i x)
        (hI x (hb hx).2.1 i)).mpr ⟨i, rfl⟩)

end PlanarNikodym
