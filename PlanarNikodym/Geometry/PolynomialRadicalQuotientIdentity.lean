import PlanarNikodym.Geometry.PolynomialDerivativeQuotient

/-! Identification of the actual derivative-gcd quotient with the actual
unique-factorization radical. Both are independently constructed objects. -/

noncomputable section
open Polynomial UniqueFactorizationMonoid

namespace PlanarNikodym

theorem polynomialDerivativeQuotient_dvd_squarefreeRadical
    (P : ℝ[X]) (hP : P ≠ 0) :
    polynomialDerivativeQuotient P ∣ polynomialSquarefreeRadical P := by
  apply dvd_normalize_iff.mpr
  exact (dvd_radical_iff
    (polynomialDerivativeQuotient_separable P hP).squarefree.isRadical hP).mpr
      (polynomialDerivativeQuotient_dvd P)

/-- The radical divides the derivative-gcd quotient. Passing to the actual
splitting field of the radical detects every irreducible factor, not just
the real linear factors. -/
theorem polynomialSquarefreeRadical_dvd_derivativeQuotient
    (P : ℝ[X]) (hP : P ≠ 0) :
    polynomialSquarefreeRadical P ∣ polynomialDerivativeQuotient P := by
  classical
  let R := polynomialSquarefreeRadical P
  let L := R.SplittingField
  let ι : ℝ →+* L := algebraMap ℝ L
  have hR : R ≠ 0 := (polynomialSquarefreeRadical_monic P).ne_zero
  have hQ := polynomialDerivativeQuotient_ne_zero P hP
  apply (Polynomial.map_dvd_map' ι).mp
  apply (Polynomial.SplittingField.splits R).dvd_of_roots_le_roots
    (Polynomial.map_ne_zero hR)
  have hnodup : (R.map ι).roots.Nodup :=
    Polynomial.nodup_roots
      ((Polynomial.separable_map ι).mpr (polynomialSquarefreeRadical_separable P))
  apply (Multiset.le_iff_subset hnodup).mpr
  intro t ht
  have htR : (R.map ι).IsRoot t :=
    (Polynomial.mem_roots (Polynomial.map_ne_zero hR)).mp ht
  have htP : (P.map ι).IsRoot t :=
    htR.dvd (Polynomial.map_dvd ι (polynomialSquarefreeRadical_dvd P))
  have htQ := (polynomialDerivativeQuotient_isRoot_iff
    (P.map ι) (Polynomial.map_ne_zero hP) t).mpr htP
  rw [← polynomialDerivativeQuotient_map] at htQ
  exact (Polynomial.mem_roots (Polynomial.map_ne_zero hQ)).mpr htQ

/-- For a monic polynomial, the literal quotient by the monic derivative gcd
is exactly the normalized product of its distinct irreducible factors. -/
theorem polynomialDerivativeQuotient_eq_squarefreeRadical
    (P : ℝ[X]) (hP : P.Monic) :
    polynomialDerivativeQuotient P = polynomialSquarefreeRadical P := by
  have hnorm := normalize_eq_normalize
    (polynomialDerivativeQuotient_dvd_squarefreeRadical P hP.ne_zero)
    (polynomialSquarefreeRadical_dvd_derivativeQuotient P hP.ne_zero)
  simpa only [(polynomialDerivativeQuotient_monic P hP).normalize_eq_self,
    (polynomialSquarefreeRadical_monic P).normalize_eq_self] using hnorm

end PlanarNikodym
