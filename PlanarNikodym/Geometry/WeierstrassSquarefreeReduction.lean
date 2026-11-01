import PlanarNikodym.Geometry.PolynomialSquarefreeRadical
import PlanarNikodym.Geometry.WeierstrassDiscriminant

/-! Actual squarefree reduction in the coefficient representation used by the
analytic root-chart theorems. This is a statement at a fixed coefficient vector;
it does not assert analytic dependence of the reduction across degree jumps. -/

noncomputable section
open Polynomial

namespace PlanarNikodym

/-- Recover every monic polynomial from its lower coefficient vector. -/
theorem weierstrassPolynomial_coeff_eq (P : ℝ[X]) (hP : P.Monic) :
    weierstrassPolynomial (fun i : Fin P.natDegree => P.coeff i) = P := by
  unfold weierstrassPolynomial
  simpa only [← Fin.sum_univ_eq_sum_range] using hP.as_sum.symm

/-- The actual collision determinant of a separable monic polynomial is nonzero. -/
theorem weierstrassCollisionDet_ne_zero_of_separable
    {m : ℕ} (a : Fin m → ℝ) (ha : (weierstrassPolynomial a).Separable) :
    weierstrassCollisionDet a ≠ 0 := by
  have h := Polynomial.resultant_ne_zero (weierstrassPolynomial a)
    (weierstrassPolynomial a).derivative ha
  simpa only [weierstrassCollisionDet, Polynomial.natDegree_derivative,
    weierstrassPolynomial_natDegree] using h

/-- Any nonzero polynomial has an actual lower-degree monic coefficient vector
with nonzero collision determinant and exactly the same complete real zero set.
No simplicity hypothesis is imposed on the original polynomial. -/
theorem exists_weierstrass_squarefree_reduction
    (P : ℝ[X]) (hP : P ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → ℝ), n ≤ P.natDegree ∧
      weierstrassPolynomial a ∣ P ∧
      weierstrassCollisionDet a ≠ 0 ∧
      ∀ t : ℝ, (weierstrassPolynomial a).eval t = 0 ↔ P.eval t = 0 := by
  let Q := polynomialSquarefreeRadical P
  let a : Fin Q.natDegree → ℝ := fun i => Q.coeff i
  have he : weierstrassPolynomial a = Q :=
    weierstrassPolynomial_coeff_eq Q (polynomialSquarefreeRadical_monic P)
  refine ⟨Q.natDegree, a, polynomialSquarefreeRadical_natDegree_le P, ?_, ?_, ?_⟩
  · rw [he]
    exact polynomialSquarefreeRadical_dvd P
  · apply weierstrassCollisionDet_ne_zero_of_separable
    rw [he]
    exact polynomialSquarefreeRadical_separable P
  · intro t
    rw [he]
    exact polynomialSquarefreeRadical_eval_eq_zero_iff P hP t

/-- An arbitrary finite monic family, including members sharing factors or
having repeated roots, has one squarefree coefficient vector whose real roots
are precisely the union of the original real root sets. -/
theorem exists_weierstrass_family_squarefree_reduction
    {J : Type*} [Fintype J] (m : J → ℕ) (a : ∀ j, Fin (m j) → ℝ) :
    ∃ (n : ℕ) (b : Fin n → ℝ), n ≤ ∑ j, m j ∧
      weierstrassPolynomial b ∣ ∏ j, weierstrassPolynomial (a j) ∧
      weierstrassCollisionDet b ≠ 0 ∧
      ∀ t : ℝ, (weierstrassPolynomial b).eval t = 0 ↔
        ∃ j, (weierstrassPolynomial (a j)).eval t = 0 := by
  classical
  have hmonic (j : J) (_ : j ∈ Finset.univ) :
      (weierstrassPolynomial (a j)).Monic := weierstrassPolynomial_monic (a j)
  have hprod : (∏ j, weierstrassPolynomial (a j)).Monic :=
    Polynomial.monic_prod_of_monic _ _ hmonic
  obtain ⟨n, b, hdeg, hdvd, hdet, hroots⟩ :=
    exists_weierstrass_squarefree_reduction _ hprod.ne_zero
  refine ⟨n, b, ?_, hdvd, hdet, ?_⟩
  · simpa only [Polynomial.natDegree_prod_of_monic _ _ hmonic,
      weierstrassPolynomial_natDegree] using hdeg
  · intro t
    rw [hroots]
    simp only [Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

end PlanarNikodym
