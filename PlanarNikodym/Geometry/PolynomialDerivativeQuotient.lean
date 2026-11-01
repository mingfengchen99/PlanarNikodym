import PlanarNikodym.Geometry.WeierstrassSquarefreeReduction
import Mathlib.FieldTheory.SplittingField.Construction

/-! Genuine repeated-factor removal by division by the derivative gcd.
The gcd is the normalized Euclidean gcd, so it is monic and commutes with
field embeddings. Separability is proved using actual root multiplicities in
the splitting field of the quotient. -/

noncomputable section
open Polynomial

namespace PlanarNikodym

variable {K : Type*} [Field K]

def polynomialDerivativeGcd (P : K[X]) : K[X] := by
  classical
  exact normalize (EuclideanDomain.gcd P P.derivative)

def polynomialDerivativeQuotient (P : K[X]) : K[X] :=
  P / polynomialDerivativeGcd P

theorem polynomialDerivativeGcd_dvd (P : K[X]) :
    polynomialDerivativeGcd P ∣ P := by
  classical
  exact normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left _ _)

theorem polynomialDerivativeGcd_dvd_derivative (P : K[X]) :
    polynomialDerivativeGcd P ∣ P.derivative := by
  classical
  exact normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right _ _)

theorem polynomialDerivativeGcd_ne_zero (P : K[X]) (hP : P ≠ 0) :
    polynomialDerivativeGcd P ≠ 0 := by
  classical
  change normalize (EuclideanDomain.gcd P P.derivative) ≠ 0
  rw [ne_eq, normalize_eq_zero]
  exact fun h => hP (EuclideanDomain.gcd_eq_zero_iff.mp h).1

theorem polynomialDerivativeGcd_monic (P : K[X]) (hP : P ≠ 0) :
    (polynomialDerivativeGcd P).Monic := by
  classical
  exact Polynomial.monic_normalize (fun h => hP (EuclideanDomain.gcd_eq_zero_iff.mp h).1)

/-- A monic gcd obtained by another exact construction agrees with the actual
normalized Euclidean gcd. This lets analytic coefficient constructions use
their own proved gcd certificates. -/
theorem polynomialDerivativeGcd_eq_of_monic_gcd
    (P G : K[X]) (hP : P ≠ 0) (hG : G.Monic)
    (hGP : G ∣ P) (hGP' : G ∣ P.derivative)
    (hgreatest : ∀ D : K[X], D ∣ P → D ∣ P.derivative → D ∣ G) :
    G = polynomialDerivativeGcd P := by
  classical
  have hleft : G ∣ polynomialDerivativeGcd P :=
    dvd_normalize_iff.mpr (EuclideanDomain.dvd_gcd hGP hGP')
  have hright := hgreatest (polynomialDerivativeGcd P)
    (polynomialDerivativeGcd_dvd P) (polynomialDerivativeGcd_dvd_derivative P)
  simpa only [hG.normalize_eq_self, (polynomialDerivativeGcd_monic P hP).normalize_eq_self]
    using normalize_eq_normalize hleft hright

theorem polynomialDerivativeGcd_mul_quotient (P : K[X]) (hP : P ≠ 0) :
    polynomialDerivativeGcd P * polynomialDerivativeQuotient P = P :=
  EuclideanDomain.mul_div_cancel' (polynomialDerivativeGcd_ne_zero P hP)
    (polynomialDerivativeGcd_dvd P)

theorem polynomialDerivativeQuotient_ne_zero (P : K[X]) (hP : P ≠ 0) :
    polynomialDerivativeQuotient P ≠ 0 := by
  intro h
  have he := polynomialDerivativeGcd_mul_quotient P hP
  rw [h, mul_zero] at he
  exact hP he.symm

theorem polynomialDerivativeQuotient_dvd (P : K[X]) :
    polynomialDerivativeQuotient P ∣ P :=
  EuclideanDomain.div_dvd_of_dvd (polynomialDerivativeGcd_dvd P)

theorem polynomialDerivativeQuotient_monic (P : K[X]) (hP : P.Monic) :
    (polynomialDerivativeQuotient P).Monic := by
  change (P / polynomialDerivativeGcd P).leadingCoeff = 1
  rw [Polynomial.leadingCoeff_div
    (Polynomial.degree_le_of_dvd (polynomialDerivativeGcd_dvd P) hP.ne_zero),
    hP.leadingCoeff, (polynomialDerivativeGcd_monic P hP.ne_zero).leadingCoeff, div_one]

theorem polynomialDerivativeQuotient_map
    {L : Type*} [Field L] (P : K[X]) (ι : K →+* L) :
    (polynomialDerivativeQuotient P).map ι =
      polynomialDerivativeQuotient (P.map ι) := by
  classical
  simp only [polynomialDerivativeQuotient, polynomialDerivativeGcd,
    Polynomial.map_div, Polynomial.map_normalize, ← Polynomial.gcd_map,
    Polynomial.derivative_map]

private theorem derivativeGcd_rootMultiplicity (P : K[X])
    (hP : P ≠ 0) (hP' : P.derivative ≠ 0) (t : K) :
    (polynomialDerivativeGcd P).rootMultiplicity t =
      min (P.rootMultiplicity t) (P.derivative.rootMultiplicity t) := by
  classical
  have hg := polynomialDerivativeGcd_ne_zero P hP
  have hiff (n : ℕ) :
      n ≤ (polynomialDerivativeGcd P).rootMultiplicity t ↔
        n ≤ P.rootMultiplicity t ∧ n ≤ P.derivative.rootMultiplicity t := by
    rw [Polynomial.le_rootMultiplicity_iff hg,
      Polynomial.le_rootMultiplicity_iff hP, Polynomial.le_rootMultiplicity_iff hP']
    change _ ∣ normalize (EuclideanDomain.gcd P P.derivative) ↔ _
    rw [dvd_normalize_iff]
    exact ⟨fun h => ⟨h.trans (EuclideanDomain.gcd_dvd_left _ _),
      h.trans (EuclideanDomain.gcd_dvd_right _ _)⟩,
      fun h => EuclideanDomain.dvd_gcd h.1 h.2⟩
  apply Nat.le_antisymm
  · exact le_min ((hiff _).mp le_rfl).1 ((hiff _).mp le_rfl).2
  · exact (hiff _).mpr ⟨min_le_left _ _, min_le_right _ _⟩

variable [CharZero K]

/-- Division by the derivative gcd leaves multiplicity exactly one at every
original root, including roots of arbitrarily high original multiplicity. -/
theorem polynomialDerivativeQuotient_rootMultiplicity
    (P : K[X]) (hP : P ≠ 0) (t : K) (ht : P.IsRoot t) :
    (polynomialDerivativeQuotient P).rootMultiplicity t = 1 := by
  have hP' : P.derivative ≠ 0 := by
    intro h
    have he := Polynomial.eq_C_of_derivative_eq_zero h
    rw [he] at ht hP
    exact hP (by simpa only [Polynomial.IsRoot, Polynomial.eval_C, Polynomial.C_eq_zero] using ht)
  have hg := derivativeGcd_rootMultiplicity P hP hP' t
  rw [Polynomial.derivative_rootMultiplicity_of_root ht,
    min_eq_right (Nat.sub_le _ _)] at hg
  have he := polynomialDerivativeGcd_mul_quotient P hP
  have hm := congrArg (fun Q : K[X] => Q.rootMultiplicity t) he
  have hmul : polynomialDerivativeGcd P * polynomialDerivativeQuotient P ≠ 0 := by
    rw [he]
    exact hP
  rw [Polynomial.rootMultiplicity_mul hmul, hg] at hm
  have hpos := (Polynomial.rootMultiplicity_pos hP).mpr ht
  omega

theorem polynomialDerivativeQuotient_isRoot_iff
    (P : K[X]) (hP : P ≠ 0) (t : K) :
    (polynomialDerivativeQuotient P).IsRoot t ↔ P.IsRoot t := by
  constructor
  · intro ht
    exact Polynomial.dvd_iff_isRoot.mp
      ((Polynomial.dvd_iff_isRoot.mpr ht).trans (polynomialDerivativeQuotient_dvd P))
  · intro ht
    apply (Polynomial.rootMultiplicity_pos (polynomialDerivativeQuotient_ne_zero P hP)).mp
    rw [polynomialDerivativeQuotient_rootMultiplicity P hP t ht]
    exact Nat.zero_lt_one

/-- The actual quotient is separable, including over fields where the original
polynomial does not split: its genuine splitting field is used in the proof. -/
theorem polynomialDerivativeQuotient_separable (P : K[X]) (hP : P ≠ 0) :
    (polynomialDerivativeQuotient P).Separable := by
  classical
  let Q := polynomialDerivativeQuotient P
  let L := Q.SplittingField
  let ι : K →+* L := algebraMap K L
  have hQ := polynomialDerivativeQuotient_ne_zero P hP
  apply (Polynomial.separable_map ι).mp
  apply (Polynomial.nodup_roots_iff_of_splits (Polynomial.map_ne_zero hQ)
    (Polynomial.SplittingField.splits Q)).mp
  apply Multiset.nodup_iff_count_le_one.mpr
  intro t
  rw [Polynomial.count_roots]
  change ((polynomialDerivativeQuotient P).map ι).rootMultiplicity t ≤ 1
  rw [polynomialDerivativeQuotient_map]
  by_cases ht : (P.map ι).IsRoot t
  · rw [polynomialDerivativeQuotient_rootMultiplicity _ (Polynomial.map_ne_zero hP) t ht]
  · rw [Polynomial.rootMultiplicity_eq_zero (fun h =>
      ht ((polynomialDerivativeQuotient_isRoot_iff _ (Polynomial.map_ne_zero hP) t).mp h))]
    exact Nat.zero_le _

omit [CharZero K] in
theorem polynomialDerivativeQuotient_natDegree_le (P : K[X]) (hP : P ≠ 0) :
    (polynomialDerivativeQuotient P).natDegree ≤ P.natDegree :=
  Polynomial.natDegree_le_of_dvd (polynomialDerivativeQuotient_dvd P) hP

theorem polynomialDerivativeQuotient_eval_eq_zero_iff
    (P : K[X]) (hP : P ≠ 0) (t : K) :
    (polynomialDerivativeQuotient P).eval t = 0 ↔ P.eval t = 0 :=
  polynomialDerivativeQuotient_isRoot_iff P hP t

/-- The actual real-valued derivative of the quotient is nonzero at all its
zeros, with no assumption on the multiplicities of the original polynomial. -/
theorem deriv_polynomialDerivativeQuotient_ne_zero
    (P : ℝ[X]) (hP : P ≠ 0) (t : ℝ)
    (ht : (polynomialDerivativeQuotient P).eval t = 0) :
    deriv (fun s => (polynomialDerivativeQuotient P).eval s) t ≠ 0 := by
  rw [Polynomial.deriv]
  simpa only [Polynomial.eval₂_id] using
    (polynomialDerivativeQuotient_separable P hP).eval₂_derivative_ne_zero
      (RingHom.id ℝ) (by simpa only [Polynomial.eval₂_id] using ht)

/-- The actual quotient's lower coefficient vector has nonzero collision
determinant. This is the coefficient-level interface for analytic gcd strata. -/
theorem collisionDet_polynomialDerivativeQuotient_ne_zero
    (P : ℝ[X]) (hP : P.Monic) :
    weierstrassCollisionDet
      (fun i : Fin (polynomialDerivativeQuotient P).natDegree =>
        (polynomialDerivativeQuotient P).coeff i) ≠ 0 := by
  apply weierstrassCollisionDet_ne_zero_of_separable
  rw [weierstrassPolynomial_coeff_eq _ (polynomialDerivativeQuotient_monic P hP)]
  exact polynomialDerivativeQuotient_separable P hP.ne_zero

/-- A packaged actual division result: the output is literally `P` divided by
its monic derivative gcd, represented by its own coefficients. -/
theorem exists_derivative_quotient_weierstrass_coefficients
    (P : ℝ[X]) (hP : P.Monic) :
    ∃ (n : ℕ) (a : Fin n → ℝ), n ≤ P.natDegree ∧
      weierstrassPolynomial a = polynomialDerivativeQuotient P ∧
      weierstrassCollisionDet a ≠ 0 ∧
      ∀ t : ℝ, (weierstrassPolynomial a).eval t = 0 ↔ P.eval t = 0 := by
  let Q := polynomialDerivativeQuotient P
  let a : Fin Q.natDegree → ℝ := fun i => Q.coeff i
  have he : weierstrassPolynomial a = Q :=
    weierstrassPolynomial_coeff_eq _ (polynomialDerivativeQuotient_monic P hP)
  refine ⟨Q.natDegree, a, polynomialDerivativeQuotient_natDegree_le P hP.ne_zero,
    he, collisionDet_polynomialDerivativeQuotient_ne_zero P hP, ?_⟩
  intro t
  rw [he]
  exact polynomialDerivativeQuotient_eval_eq_zero_iff P hP.ne_zero t

end PlanarNikodym
