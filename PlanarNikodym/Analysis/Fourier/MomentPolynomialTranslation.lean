import PlanarNikodym.Analysis.Fourier.LowerDegreePhaseScaling
import Mathlib.RingTheory.Polynomial.DegreeLT

/-! Exact recentering of the constant-coefficient moment model. The map
is constructed by translating an actual polynomial, so its inverse and
composition laws do not require an analytic estimate. -/

noncomputable section
open scoped BigOperators Nat
namespace PlanarNikodym

def jetCoefficientPolynomial (n : ℕ) :
    Aux (n + 1) ≃ₗ[ℝ] Polynomial.degreeLT ℝ (n + 1) :=
  (coefficientDilation (fun j : Fin (n + 1) => (((j : ℕ)! : ℝ))⁻¹)
    (by intro j; positivity)).toLinearEquiv.trans (Polynomial.degreeLTEquiv ℝ (n + 1)).symm

theorem jetCoefficientPolynomial_eval {n : ℕ} (w : Aux (n + 1)) (t : ℝ) :
    (jetCoefficientPolynomial n w).val.eval t = jetPolynomial w t := by
  change (∑ j : Fin (n + 1), Polynomial.monomial (j : ℕ)
    ((((j : ℕ)! : ℝ))⁻¹ * w j)).eval t = _
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, jetPolynomial]
  apply Finset.sum_congr rfl
  intro j _
  ring

def momentTranslation (n : ℕ) (c : ℝ) : Aux (n + 1) ≃L[ℝ] Aux (n + 1) :=
  ((jetCoefficientPolynomial n).trans
    ((Polynomial.taylorLinearEquiv c (n + 1)).trans (jetCoefficientPolynomial n).symm)
    ).toContinuousLinearEquiv

theorem jetPolynomial_momentTranslation {n : ℕ} (c : ℝ) (w : Aux (n + 1)) (t : ℝ) :
    jetPolynomial (momentTranslation n c w) t = jetPolynomial w (c + t) := by
  rw [← jetCoefficientPolynomial_eval, ← jetCoefficientPolynomial_eval]
  change ((jetCoefficientPolynomial n) ((jetCoefficientPolynomial n).symm
    (Polynomial.taylorLinearEquiv c (n + 1) (jetCoefficientPolynomial n w)))).val.eval t = _
  rw [LinearEquiv.apply_symm_apply]
  change (Polynomial.taylor c (jetCoefficientPolynomial n w).val).eval t = _
  rw [Polynomial.taylor_eval, add_comm t c]

theorem momentTranslation_symm (n : ℕ) (c : ℝ) :
    (momentTranslation n c).symm = momentTranslation n (-c) := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  change ((jetCoefficientPolynomial n).trans ((Polynomial.taylorLinearEquiv c (n + 1)).trans
    (jetCoefficientPolynomial n).symm)).symm = (jetCoefficientPolynomial n).trans
      ((Polynomial.taylorLinearEquiv (-c) (n + 1)).trans (jetCoefficientPolynomial n).symm)
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    Polynomial.taylorLinearEquiv_symm]
  rfl

theorem det_momentTranslation (n : ℕ) (c : ℝ) :
    LinearMap.det (momentTranslation n c).toLinearMap = 1 := by
  change LinearMap.det (((jetCoefficientPolynomial n).symm.toLinearMap.comp
    (Polynomial.taylorLinearEquiv c (n + 1)).toLinearMap).comp
      (jetCoefficientPolynomial n).toLinearMap) = 1
  have he := LinearMap.det_conj
    (Polynomial.taylorLinearEquiv c (n + 1)).toLinearMap (jetCoefficientPolynomial n).symm
  simpa only [LinearEquiv.symm_symm, LinearMap.comp_assoc] using
    he.trans (Polynomial.det_taylorLinearEquiv_toLinearMap (r := c) (n := n + 1))

end PlanarNikodym
