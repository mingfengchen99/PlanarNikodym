import PlanarNikodym.Analysis.Fourier.TimeTaylorApproximation
import PlanarNikodym.Analysis.Jets.CompactParameterIntegral

/-! The time Taylor remainder divided by the appropriate power of the
time increment has an actual smooth extension through increment zero.
This retains all parameter and time derivatives, rather than only a
function-value remainder estimate. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval Nat

namespace PlanarNikodym

/-- The normalized remainder is defined by an integral over a fixed
interval. Its arguments are the parameter, Taylor center and increment. -/
def timeTaylorIntegralRemainder {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ)
    (x : P × ℝ × ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ((1 - s) ^ n / (n ! : ℝ)) *
    iteratedPartialTimeDeriv (n + 1) Φ (x.1, x.2.1 + x.2.2 * s)

theorem contDiff_timeTaylorIntegralRemainder
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ) :
    ContDiff ℝ ∞ (timeTaylorIntegralRemainder Φ n) := by
  have hD : ContDiff ℝ ∞ (iteratedPartialTimeDeriv (n + 1) Φ) :=
    contDiff_iff_contDiffAt.mpr (fun _ =>
      contDiffAt_iteratedPartialTimeDeriv hΦ.contDiffAt (n + 1))
  have harg : ContDiff ℝ ∞ (fun q : (P × ℝ × ℝ) × ℝ =>
      (q.1.1, q.1.2.1 + q.1.2.2 * q.2)) := by fun_prop
  have hw : ContDiff ℝ ∞ (fun q : (P × ℝ × ℝ) × ℝ =>
      (1 - q.2) ^ n / (n ! : ℝ)) := by fun_prop
  exact contDiff_intervalIntegral_of_joint_contDiff (hw.mul (hD.comp harg)) 0 1

/-- Exact Taylor formula, also valid at zero increment. -/
theorem timeTaylor_remainder_eq_integral
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ) (p : P) (c h : ℝ) :
    Φ (p, c + h) - timeTaylorEval Φ n p c (c + h) =
      h ^ (n + 1) * timeTaylorIntegralRemainder Φ n (p, c, h) := by
  by_cases hh : h = 0
  · subst h
    simp
  have hct : c ≠ c + h := by intro he; apply hh; linarith
  have hs : ContDiff ℝ ∞ (fun s => Φ (p, s)) :=
    hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hu : UniqueDiffOn ℝ (uIcc c (c + h)) := uniqueDiffOn_Icc (by grind)
  rw [timeTaylorEval_eq_taylorWithinEval Φ n p hct hs.contDiffAt,
    taylor_integral_remainder (contDiff_infty.mp hs (n + 1)).contDiffOn]
  let F : ℝ → ℝ := fun s => ((c + h - s) ^ n / (n ! : ℝ)) *
    iteratedPartialTimeDeriv (n + 1) Φ (p, s)
  have he : (∫ s in c..c + h, ((c + h - s) ^ n / (n ! : ℝ)) •
      iteratedDerivWithin (n + 1) (fun s => Φ (p, s)) (uIcc c (c + h)) s) =
      ∫ s in c..c + h, F s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (contDiff_infty.mp hs (n + 1)).contDiffAt hs',
      ← iteratedPartialTimeDeriv_apply]
    rfl
  rw [he]
  have hchange := intervalIntegral.smul_integral_comp_add_mul F h c (a := 0) (b := 1)
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul] at hchange
  rw [← hchange]
  have hfun : (fun s : ℝ => F (c + h * s)) = fun s => h ^ n *
      (((1 - s) ^ n / (n ! : ℝ)) *
        iteratedPartialTimeDeriv (n + 1) Φ (p, c + h * s)) := by
    funext s
    dsimp only [F]
    rw [show c + h - (c + h * s) = h * (1 - s) by ring, mul_pow]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  simp only [timeTaylorIntegralRemainder]
  ring

/-- All joint jets of the normalized remainder are bounded on any fixed
compact set, including points with zero increment. -/
theorem exists_uniform_timeTaylorIntegralRemainder_jet_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n m : ℕ)
    {K : Set (P × ℝ × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (timeTaylorIntegralRemainder Φ n) x‖ ≤ C := by
  have hR := contDiff_timeTaylorIntegralRemainder hΦ n
  have hJ := (contDiff_infty.mp hR m).continuous_iteratedFDeriv (m := m) le_rfl
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hJ.continuousOn
  exact ⟨|B|, abs_nonneg _, fun x hx => (hB x hx).trans (le_abs_self B)⟩

/-- A smooth profile for the frequency-weighted error after the change
of time variable `t = c + δ τ`. The variable `α` stands for `λ δ^(n+1)`. -/
def scaledTimeTaylorErrorProfile {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ)
    (q : (P × ℝ × ℝ) × ℝ × ℝ) : ℝ :=
  q.2.1 * q.1.2.2 ^ (n + 1) *
    timeTaylorIntegralRemainder Φ n (q.1.1, q.1.2.1, q.2.2 * q.1.2.2)

theorem contDiff_scaledTimeTaylorErrorProfile
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ) :
    ContDiff ℝ ∞ (scaledTimeTaylorErrorProfile Φ n) := by
  have ha : ContDiff ℝ ∞ (fun q : (P × ℝ × ℝ) × ℝ × ℝ =>
      (q.1.1, q.1.2.1, q.2.2 * q.1.2.2)) := by fun_prop
  exact (contDiff_snd.fst.mul (contDiff_fst.snd.snd.pow (n + 1))).mul
    ((contDiff_timeTaylorIntegralRemainder hΦ n).comp ha)

theorem scaledTimeTaylorErrorProfile_eq
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ)
    (p : P) (c τ r δ : ℝ) :
    scaledTimeTaylorErrorProfile Φ n ((p, c, τ), r * δ ^ (n + 1), δ) =
      r * (Φ (p, c + δ * τ) - timeTaylorEval Φ n p c (c + δ * τ)) := by
  rw [timeTaylor_remainder_eq_integral hΦ]
  simp only [scaledTimeTaylorErrorProfile, mul_pow]
  ring

end PlanarNikodym
