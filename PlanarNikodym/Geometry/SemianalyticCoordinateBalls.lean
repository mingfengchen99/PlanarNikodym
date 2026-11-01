import PlanarNikodym.Geometry.SemianalyticGerms
import Mathlib.Analysis.Normed.Group.Constructions

noncomputable section
open Set Filter Metric
namespace PlanarNikodym

theorem locallySemianalytic_coordinate_ball {n : ℕ} (c : Fin n → ℝ) (r : ℝ) (hr : 0 < r) :
    LocallySemianalytic (ball c r) := by
  let f : Fin n ⊕ Fin n → (Fin n → ℝ) → ℝ :=
    Sum.elim (fun i x => r - (x i - c i)) (fun i x => r + (x i - c i))
  intro x
  have ha (j : Fin n ⊕ Fin n) : AnalyticAt ℝ (f j) x := by
    rcases j with i | i
    · exact analyticAt_const.sub
        (((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt x).sub analyticAt_const)
    · exact analyticAt_const.add
        (((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt x).sub analyticAt_const)
  have hsg := semianalyticAt_of_analytic_sign_germs f ha (fun s => ∀ j, s j = 2)
  apply hsg.congr
  apply Filter.Eventually.of_forall
  intro y
  change (∀ j, oneDimensionalSign (f j y) = 2) ↔ y ∈ ball c r
  rw [mem_ball, dist_pi_lt_iff hr]
  constructor
  · intro hy i
    have hl := oneDimensionalSign_eq_two.mp (hy (Sum.inl i))
    have hu := oneDimensionalSign_eq_two.mp (hy (Sum.inr i))
    rw [Real.dist_eq, abs_lt]
    dsimp [f] at hl hu
    constructor <;> linarith
  · intro hy j
    rcases j with i | i
    · apply oneDimensionalSign_eq_two.mpr
      have hi := abs_lt.mp (show |y i - c i| < r by simpa only [Real.dist_eq] using hy i)
      dsimp [f]
      linarith [hi.2]
    · apply oneDimensionalSign_eq_two.mpr
      have hi := abs_lt.mp (show |y i - c i| < r by simpa only [Real.dist_eq] using hy i)
      dsimp [f]
      linarith [hi.1]

end PlanarNikodym
