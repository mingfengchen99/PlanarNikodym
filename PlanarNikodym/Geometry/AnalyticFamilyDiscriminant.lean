import PlanarNikodym.Geometry.WeierstrassDiscriminant

/-! One actual analytic collision function for a finite monic polynomial family.
Its nonzero locus has simple roots for every member and no shared roots between
different members. The determinant is not assumed to be nontrivial as a germ. -/

noncomputable section
open Set Filter
open scoped Topology

namespace PlanarNikodym

def weierstrassFamilyCollisionDet {J : Type*} [Fintype J]
    (m : J → ℕ) (a : ∀ j, Fin (m j) → ℝ) : ℝ := by
  classical
  exact (∏ j, weierstrassCollisionDet (a j)) *
    ∏ j, ∏ k, if j = k then 1 else weierstrassPairResultant (a j) (a k)

theorem analyticAt_weierstrassFamilyCollisionDet
    {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : J → ℕ) (a : E → ∀ j, Fin (m j) → ℝ) (x : E)
    (ha : ∀ j, AnalyticAt ℝ (fun y => a y j) x) :
    AnalyticAt ℝ (fun y => weierstrassFamilyCollisionDet m (a y)) x := by
  classical
  unfold weierstrassFamilyCollisionDet
  apply AnalyticAt.mul
  · apply Finset.analyticAt_fun_prod
    intro j _
    exact analyticAt_weierstrassCollisionDet _ x (ha j)
  · apply Finset.analyticAt_fun_prod
    intro j _
    apply Finset.analyticAt_fun_prod
    intro k _
    split_ifs
    · exact analyticAt_const
    · exact analyticAt_weierstrassPairResultant _ _ x (ha j) (ha k)

/-- Nonzero finite-family collision determinant gives actual simple roots and
pairwise disjoint root sets. Empty families and degree-zero members are allowed. -/
theorem simple_disjoint_roots_of_weierstrassFamilyCollisionDet_ne_zero
    {J : Type*} [Fintype J] (m : J → ℕ) (a : ∀ j, Fin (m j) → ℝ)
    (hdet : weierstrassFamilyCollisionDet m a ≠ 0) :
    (∀ j t, (weierstrassPolynomial (a j)).eval t = 0 →
      deriv (fun s => (weierstrassPolynomial (a j)).eval s) t ≠ 0) ∧
    ∀ j k, j ≠ k → ∀ t, ¬ ((weierstrassPolynomial (a j)).eval t = 0 ∧
      (weierstrassPolynomial (a k)).eval t = 0) := by
  classical
  have h := mul_ne_zero_iff.mp hdet
  constructor
  · intro j t ht
    exact deriv_ne_zero_of_weierstrassCollisionDet_ne_zero (a j)
      (Finset.prod_ne_zero_iff.mp h.1 j (Finset.mem_univ j)) t ht
  · intro j k hjk t
    have hj := Finset.prod_ne_zero_iff.mp h.2 j (Finset.mem_univ j)
    have hk := Finset.prod_ne_zero_iff.mp hj k (Finset.mem_univ k)
    rw [if_neg hjk] at hk
    exact no_common_root_of_weierstrassPairResultant_ne_zero (a j) (a k) hk t

/-- An actual multiple root or a root shared by two distinct members forces
the analytic finite-family collision function to vanish. -/
theorem weierstrassFamilyCollisionDet_eq_zero_of_collision
    {J : Type*} [Fintype J] (m : J → ℕ) (a : ∀ j, Fin (m j) → ℝ)
    (hcollision :
      (∃ j t, (weierstrassPolynomial (a j)).eval t = 0 ∧
        deriv (fun s => (weierstrassPolynomial (a j)).eval s) t = 0) ∨
      ∃ j k, j ≠ k ∧ ∃ t, (weierstrassPolynomial (a j)).eval t = 0 ∧
        (weierstrassPolynomial (a k)).eval t = 0) :
    weierstrassFamilyCollisionDet m a = 0 := by
  by_contra hn
  obtain ⟨hs, hd⟩ := simple_disjoint_roots_of_weierstrassFamilyCollisionDet_ne_zero m a hn
  rcases hcollision with ⟨j, t, ht, hdt⟩ | ⟨j, k, hjk, t, hjt, hkt⟩
  · exact hs j t ht hdt
  · exact hd j k hjk t ⟨hjt, hkt⟩

end PlanarNikodym
