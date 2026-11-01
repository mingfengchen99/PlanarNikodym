import PlanarNikodym.Geometry.WeierstrassPolynomial
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.FieldTheory.Perfect
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Removing repeated and shared factors from actual real polynomials.
The normalized unique-factorization radical preserves the complete real zero
set of a nonzero polynomial and has nonzero derivative at every real root.
No assertion of analytic dependence on varying coefficients is made here. -/

noncomputable section
open Polynomial UniqueFactorizationMonoid

namespace PlanarNikodym

/-- The actual normalized product of the distinct irreducible factors. -/
def polynomialSquarefreeRadical (P : ℝ[X]) : ℝ[X] :=
  normalize (radical P)

theorem polynomialSquarefreeRadical_monic (P : ℝ[X]) :
    (polynomialSquarefreeRadical P).Monic := by
  classical
  exact Polynomial.monic_normalize radical_ne_zero

theorem polynomialSquarefreeRadical_squarefree (P : ℝ[X]) :
    Squarefree (polynomialSquarefreeRadical P) := by
  exact (associated_normalize (radical P)).squarefree_iff.mp squarefree_radical

theorem polynomialSquarefreeRadical_dvd (P : ℝ[X]) :
    polynomialSquarefreeRadical P ∣ P := by
  exact normalize_dvd_iff.mpr radical_dvd_self

theorem polynomialSquarefreeRadical_natDegree_le (P : ℝ[X]) :
    (polynomialSquarefreeRadical P).natDegree ≤ P.natDegree := by
  classical
  exact (Polynomial.natDegree_le_of_dvd (normalize_dvd_iff.mpr dvd_rfl)
    radical_ne_zero).trans natDegree_radical_le

/-- Repeated factors may be deleted without changing any real zero. The
nonzero hypothesis is essential, since the radical of zero is one. -/
theorem polynomialSquarefreeRadical_eval_eq_zero_iff
    (P : ℝ[X]) (hP : P ≠ 0) (t : ℝ) :
    (polynomialSquarefreeRadical P).eval t = 0 ↔ P.eval t = 0 := by
  change (polynomialSquarefreeRadical P).IsRoot t ↔ P.IsRoot t
  rw [← Polynomial.dvd_iff_isRoot, ← Polynomial.dvd_iff_isRoot]
  exact dvd_normalize_iff.trans
    (dvd_radical_iff_of_irreducible (Polynomial.irreducible_X_sub_C t) hP)

/-- In characteristic zero the genuine squarefree radical is separable. -/
theorem polynomialSquarefreeRadical_separable (P : ℝ[X]) :
    (polynomialSquarefreeRadical P).Separable :=
  PerfectField.separable_iff_squarefree.mpr (polynomialSquarefreeRadical_squarefree P)

/-- Every real zero of the radical has nonzero actual derivative. -/
theorem deriv_polynomialSquarefreeRadical_ne_zero
    (P : ℝ[X]) (t : ℝ) (ht : (polynomialSquarefreeRadical P).eval t = 0) :
    deriv (fun s => (polynomialSquarefreeRadical P).eval s) t ≠ 0 := by
  rw [Polynomial.deriv]
  simpa only [Polynomial.eval₂_id] using
    (polynomialSquarefreeRadical_separable P).eval₂_derivative_ne_zero
      (RingHom.id ℝ) (by simpa only [Polynomial.eval₂_id] using ht)

/-- A concrete squarefree replacement exists for every nonzero polynomial,
with degree bound, divisibility, the same real zero set and simple real roots. -/
theorem exists_monic_squarefree_polynomial_with_same_real_zeros
    (P : ℝ[X]) (hP : P ≠ 0) :
    ∃ Q : ℝ[X], Q.Monic ∧ Squarefree Q ∧ Q ∣ P ∧
      Q.natDegree ≤ P.natDegree ∧
      (∀ t : ℝ, Q.eval t = 0 ↔ P.eval t = 0) ∧
      ∀ t : ℝ, Q.eval t = 0 → deriv (fun s => Q.eval s) t ≠ 0 :=
  ⟨polynomialSquarefreeRadical P, polynomialSquarefreeRadical_monic P,
    polynomialSquarefreeRadical_squarefree P, polynomialSquarefreeRadical_dvd P,
    polynomialSquarefreeRadical_natDegree_le P,
    polynomialSquarefreeRadical_eval_eq_zero_iff P hP,
    deriv_polynomialSquarefreeRadical_ne_zero P⟩

/-- The radical of the actual finite product removes repetitions both within
members and between members. No discriminant nonvanishing is assumed. -/
theorem exists_squarefree_radical_of_weierstrass_family
    {J : Type*} [Fintype J] (m : J → ℕ) (a : ∀ j, Fin (m j) → ℝ) :
    ∃ Q : ℝ[X], Q.Monic ∧ Squarefree Q ∧
      Q ∣ ∏ j, weierstrassPolynomial (a j) ∧
      Q.natDegree ≤ (∏ j, weierstrassPolynomial (a j)).natDegree ∧
      (∀ t : ℝ, Q.eval t = 0 ↔ ∃ j, (weierstrassPolynomial (a j)).eval t = 0) ∧
      ∀ t : ℝ, Q.eval t = 0 → deriv (fun s => Q.eval s) t ≠ 0 := by
  classical
  have hprod : (∏ j, weierstrassPolynomial (a j)).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => weierstrassPolynomial_monic (a j))
  obtain ⟨Q, hQ, hsq, hdvd, hdeg, hroots, hsimple⟩ :=
    exists_monic_squarefree_polynomial_with_same_real_zeros _ hprod.ne_zero
  refine ⟨Q, hQ, hsq, hdvd, hdeg, ?_, hsimple⟩
  intro t
  rw [hroots]
  simp only [Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

end PlanarNikodym
