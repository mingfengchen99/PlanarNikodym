import PlanarNikodym.Geometry.AnalyticPolynomialDerivativeNormalization
import PlanarNikodym.Geometry.AnalyticPolynomialRootBranches

noncomputable section
open Polynomial
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_joint_weierstrass_iterated_derivative_eval
    {m : ℕ} (a : E → Fin m → ℝ) (k : ℕ) (x : E) (t : ℝ)
    (ha : AnalyticAt ℝ a x) :
    AnalyticAt ℝ (fun z : E × ℝ =>
      (derivative^[k] (weierstrassPolynomial (a z.1))).eval z.2) (x, t) := by
  have he : (fun z : E × ℝ => (derivative^[k] (weierstrassPolynomial (a z.1))).eval z.2) =
      fun z => ((m.descFactorial k : ℝ) *
        (weierstrassPolynomial (weierstrassIteratedDerivativeCoefficients a k z.1)).eval z.2) := by
    funext z
    rw [weierstrass_iterated_derivative_normalization, eval_mul, eval_C]
  rw [he]
  exact analyticAt_const.mul (analyticAt_joint_weierstrassPolynomial_eval _ x t
    (analyticAt_weierstrassIteratedDerivativeCoefficients a k x ha))

end PlanarNikodym
