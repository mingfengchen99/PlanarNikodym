import PlanarNikodym.Geometry.AnalyticFamilyDiscriminant

/-! Actual derivatives of finite products at simple, pairwise disjoint roots.
This supplies the simple-root hypothesis for a single product function from
the analytic collision determinant of the original polynomial family. -/

noncomputable section
open Set Filter
open scoped Topology

namespace PlanarNikodym

/-- A zero of a finite product is simple when all factors are differentiable,
the factors vanishing there have nonzero derivative, and two factors cannot
vanish there simultaneously. Empty products have no zeros. -/
theorem deriv_finset_product_ne_zero_of_simple_disjoint_roots
    {J : Type*} [Fintype J] (f : J → ℝ → ℝ) (t : ℝ)
    (hf : ∀ j, DifferentiableAt ℝ (f j) t)
    (hsimple : ∀ j, f j t = 0 → deriv (f j) t ≠ 0)
    (hdisjoint : ∀ j k, j ≠ k → ¬ (f j t = 0 ∧ f k t = 0))
    (ht : ∏ j, f j t = 0) :
    deriv (fun s => ∏ j, f j s) t ≠ 0 := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp ht
  have hothers : ∏ k ∈ Finset.univ.erase j, f k t ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk hkt
    exact hdisjoint j k (Ne.symm (Finset.mem_erase.mp hk).1) ⟨hj, hkt⟩
  have he : (fun s => ∏ i, f i s) =
      (fun s => f j s * ∏ i ∈ Finset.univ.erase j, f i s) := by
    funext s
    exact (Finset.mul_prod_erase Finset.univ (fun i => f i s)
      (Finset.mem_univ j)).symm
  rw [he, deriv_fun_mul (hf j)
      (DifferentiableAt.fun_finsetProd (u := Finset.univ.erase j) (fun i _ => hf i)),
    hj, zero_mul, add_zero]
  exact mul_ne_zero (hsimple j hj) hothers

/-- The finite-family collision determinant controls the derivative of the
actual product of all polynomial evaluations. -/
theorem deriv_weierstrassFamilyProduct_ne_zero_of_collisionDet_ne_zero
    {J : Type*} [Fintype J] (m : J → ℕ) (a : ∀ j, Fin (m j) → ℝ)
    (hdet : weierstrassFamilyCollisionDet m a ≠ 0) (t : ℝ)
    (ht : ∏ j, (weierstrassPolynomial (a j)).eval t = 0) :
    deriv (fun s => ∏ j, (weierstrassPolynomial (a j)).eval s) t ≠ 0 := by
  obtain ⟨hs, hd⟩ := simple_disjoint_roots_of_weierstrassFamilyCollisionDet_ne_zero m a hdet
  exact deriv_finset_product_ne_zero_of_simple_disjoint_roots
    (fun j s => (weierstrassPolynomial (a j)).eval s) t
    (fun j => (weierstrassPolynomial (a j)).differentiableAt)
    (fun j => hs j t) (fun j k hjk => hd j k hjk t) ht

/-- The actual product evaluation is jointly analytic in parameters and the
root variable, directly from the original analytic coefficient vectors. -/
theorem analyticAt_joint_weierstrassFamilyProduct
    {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : J → ℕ) (a : E → ∀ j, Fin (m j) → ℝ) (x₀ : E) (t₀ : ℝ)
    (ha : ∀ j, AnalyticAt ℝ (fun x => a x j) x₀) :
    AnalyticAt ℝ
      (fun z : E × ℝ => ∏ j, (weierstrassPolynomial (a z.1 j)).eval z.2)
      (x₀, t₀) := by
  classical
  apply Finset.analyticAt_fun_prod
  intro j _
  simp only [weierstrassPolynomial_eval]
  apply (analyticAt_snd.pow (m j)).add
  apply Finset.analyticAt_fun_sum
  intro i _
  have hai : AnalyticAt ℝ (fun z : E × ℝ => a z.1 j i) (x₀, t₀) :=
    AnalyticAt.comp (x := (x₀, t₀)) (f := fun z : E × ℝ => z.1)
      (g := fun x => a x j i) (analyticAt_pi_iff.mp (ha j) i) analyticAt_fst
  exact hai.mul (analyticAt_snd.pow (i : ℕ))

end PlanarNikodym
