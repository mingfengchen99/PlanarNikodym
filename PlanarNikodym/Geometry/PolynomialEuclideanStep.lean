import PlanarNikodym.Geometry.AnalyticPolynomialDegreeStrata
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Actual Euclidean remainder steps preserve common divisors, including degree
zero and degree-drop strata. Monic normalization changes only a nonzero scalar. -/

noncomputable section
open Set Polynomial
namespace PlanarNikodym

/-- Actual monic division preserves precisely the common divisors. This
algebraic identity does not require a monicity hypothesis. -/
theorem polynomial_common_divisors_modByMonic (P Q D : ℝ[X]) :
    (D ∣ Q ∧ D ∣ P %ₘ Q) ↔ (D ∣ P ∧ D ∣ Q) := by
  constructor
  · rintro ⟨hQ, hR⟩
    refine ⟨?_, hQ⟩
    rw [← Polynomial.modByMonic_add_div P Q]
    exact dvd_add hR (hQ.trans (dvd_mul_right Q (P /ₘ Q)))
  · rintro ⟨hP, hQ⟩
    refine ⟨hQ, ?_⟩
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    exact dvd_sub hP (hQ.trans (dvd_mul_right Q (P /ₘ Q)))

/-- On an actual degree stratum, monic normalization preserves all polynomial
divisors, not only the real zero set. -/
theorem polynomial_monic_normalization_divisors_iff
    {E : Type*} (p : E → ℝ[X]) (d : ℕ) (x : E)
    (hx : x ∈ polynomialDegreeStratum p d) (D : ℝ[X]) :
    D ∣ weierstrassPolynomial (polynomialMonicCoefficients p d x) ↔ D ∣ p x := by
  conv_rhs => rw [polynomial_eq_leading_mul_monic_on_stratum p d x hx]
  exact (Polynomial.dvd_C_mul hx.1).symm

/-- A zero actual remainder terminates the Euclidean step with the second
monic polynomial as a greatest common divisor, expressed by its divisor property. -/
theorem polynomial_common_divisors_of_monic_remainder_zero
    {M N : ℕ} (a : Fin M → ℝ) (b : Fin N → ℝ)
    (hz : weierstrassPolynomial a %ₘ weierstrassPolynomial b = 0) (D : ℝ[X]) :
    D ∣ weierstrassPolynomial b ↔
      D ∣ weierstrassPolynomial a ∧ D ∣ weierstrassPolynomial b := by
  simpa only [hz, dvd_zero, and_true] using
    polynomial_common_divisors_modByMonic (weierstrassPolynomial a)
      (weierstrassPolynomial b) D

/-- A nonzero remainder on its exact degree stratum can be replaced by its
actual monic normalization in the next Euclidean step. -/
theorem polynomial_common_divisors_of_monic_remainder_stratum
    {E : Type*} {M N : ℕ} (a : E → Fin M → ℝ) (b : E → Fin N → ℝ)
    (d : ℕ) (x : E)
    (hx : x ∈ polynomialDegreeStratum
      (fun y => weierstrassPolynomial (a y) %ₘ weierstrassPolynomial (b y)) d)
    (D : ℝ[X]) :
    (D ∣ weierstrassPolynomial (b x) ∧
      D ∣ weierstrassPolynomial (polynomialMonicCoefficients
        (fun y => weierstrassPolynomial (a y) %ₘ weierstrassPolynomial (b y)) d x)) ↔
        D ∣ weierstrassPolynomial (a x) ∧ D ∣ weierstrassPolynomial (b x) := by
  rw [polynomial_monic_normalization_divisors_iff _ d x hx D]
  exact polynomial_common_divisors_modByMonic _ _ D

/-- The actual remainder of a monic degree-`N` divisor has all coefficients
of order at least `N` zero. This includes `N = 0`, where the remainder is zero. -/
theorem polynomial_monic_remainder_coeff_eq_zero
    {E : Type*} {M N : ℕ} (a : E → Fin M → ℝ) (b : E → Fin N → ℝ)
    (x : E) (k : ℕ) (hk : N ≤ k) :
    (weierstrassPolynomial (a x) %ₘ weierstrassPolynomial (b x)).coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_degree_lt
  have h := Polynomial.degree_modByMonic_lt (weierstrassPolynomial (a x))
    (weierstrassPolynomial_monic (b x))
  rw [Polynomial.degree_eq_natDegree (weierstrassPolynomial_monic (b x)).ne_zero,
    weierstrassPolynomial_natDegree] at h
  exact h.trans_le (by exact_mod_cast hk)

/-- Every nonzero remainder stratum has degree strictly smaller than the
current monic divisor. This is the actual well-founded Euclidean descent. -/
theorem polynomial_monic_remainder_stratum_lt
    {E : Type*} {M N : ℕ} (a : E → Fin M → ℝ) (b : E → Fin N → ℝ)
    (d : ℕ) (x : E)
    (hx : x ∈ polynomialDegreeStratum
      (fun y => weierstrassPolynomial (a y) %ₘ weierstrassPolynomial (b y)) d) :
    d < N := by
  by_contra h
  exact hx.1 (polynomial_monic_remainder_coeff_eq_zero a b x d (Nat.le_of_not_gt h))

end PlanarNikodym
