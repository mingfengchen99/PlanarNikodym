import PlanarNikodym.Analysis.Fourier.GlyzProjectedCoordinates
import Mathlib.Analysis.Calculus.Taylor

/-! Actual Taylor polynomials and all their derivative errors. This is
the geometric Taylor comparison for the projected lower-degree curves. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def glyzTaylorCurve (f : ℝ → E) (n : ℕ) (c : ℝ) : ℝ → E := taylorWithinEval f n univ c

theorem deriv_glyzTaylorCurve (f : ℝ → E) (n : ℕ) (c : ℝ) :
    deriv (glyzTaylorCurve f (n + 1) c) = glyzTaylorCurve (deriv f) n c := by
  funext x
  simpa only [glyzTaylorCurve, derivWithin_univ] using
    (hasDerivAt_taylorWithinEval_succ (x₀ := c) (x := x) (s := univ) f n).deriv

theorem iteratedDeriv_glyzTaylorCurve_add (f : ℝ → E) (n j : ℕ) (c : ℝ) :
    iteratedDeriv j (glyzTaylorCurve f (n + j) c) = glyzTaylorCurve (iteratedDeriv j f) n c := by
  induction j generalizing f with
  | zero => simp only [Nat.add_zero, iteratedDeriv_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ', show n + (j + 1) = (n + j) + 1 by omega,
      deriv_glyzTaylorCurve, ih, ← iteratedDeriv_succ']

theorem iteratedDeriv_glyzTaylorCurve (f : ℝ → E) {n j : ℕ} (hj : j ≤ n) (c : ℝ) :
    iteratedDeriv j (glyzTaylorCurve f n c) = glyzTaylorCurve (iteratedDeriv j f) (n - j) c := by
  have h := iteratedDeriv_glyzTaylorCurve_add f (n - j) j c
  simpa only [Nat.sub_add_cancel hj] using h

theorem glyz_iteratedDeriv_order_add (f : ℝ → E) (n j : ℕ) :
    iteratedDeriv n (iteratedDeriv j f) = iteratedDeriv (n + j) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem glyz_taylor_remainder_bound (f : ℝ → E) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) {a b C s : ℝ} (hab : a < b) (hs : s ∈ Icc a b)
    (hC : ∀ u ∈ Icc a b, ‖iteratedDeriv (n + 1) f u‖ ≤ C) :
    ‖f s - glyzTaylorCurve f n a s‖ ≤ C * (s - a) ^ (n + 1) / n.factorial := by
  have hp : taylorWithinEval f n (Icc a b) a s = glyzTaylorCurve f n a s := by
    unfold glyzTaylorCurve
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))) (left_mem_Icc.mpr hab.le), iteratedDerivWithin_univ]
  rw [← hp]
  apply taylor_mean_remainder_bound hab.le (hf.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffOn hs
  intro u hu
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
    (hf.contDiffAt.of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))) hu]
  exact hC u hu

theorem exists_uniform_glyzCoordinateCurve_taylor_bound (l r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t a b : ℝ,
      a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 → a < b →
      ∀ s ∈ Icc a b, ∀ j ≤ l,
        ‖iteratedDeriv j (glyzCoordinateCurve l r t) s -
          iteratedDeriv j (glyzTaylorCurve (glyzCoordinateCurve l r t) l a) s‖ ≤
            C * (s - a) ^ (l - j + 1) / (l - j).factorial := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_glyzOrthogonalCurve_derivative_bound l r (l + 1)
  refine ⟨C, hC, ?_⟩
  intro t a b ha hb' hab s hs j hj
  rw [iteratedDeriv_glyzTaylorCurve _ hj]
  have hfj : ContDiff ℝ ∞ (iteratedDeriv j (glyzCoordinateCurve l r t)) := by
    simpa only [iteratedDeriv_eq_iterate] using
      (contDiff_glyzCoordinateCurve l r t).iterate_deriv j
  apply glyz_taylor_remainder_bound _ hfj (l - j) hab hs
  intro u hu
  rw [glyz_iteratedDeriv_order_add, show l - j + 1 + j = l + 1 by omega,
    iteratedDeriv_glyzCoordinateCurve, LinearIsometryEquiv.norm_map]
  exact hb t u ⟨ha.1.trans hu.1, hu.2.trans hb'.2⟩ (l + 1) le_rfl

end PlanarNikodym
