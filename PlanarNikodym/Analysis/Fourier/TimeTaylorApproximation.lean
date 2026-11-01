import PlanarNikodym.Analysis.Fourier.UniformNonstationaryPhase
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Uniform time Taylor remainders obtained from actual derivatives on a
joint compact set. These function-value estimates alone do not assert that
oscillatory phase errors can be discarded in a decoupling argument. -/

noncomputable section
open Set
open scoped ContDiff Interval Nat

namespace PlanarNikodym

/-- Actual iterated differentiation in the time variable, retaining the
other variables as joint parameters. -/
def iteratedPartialTimeDeriv {P : Type} (n : ℕ) (Φ : P × ℝ → ℝ) : P × ℝ → ℝ :=
  match n with
  | 0 => Φ
  | n + 1 => partialTimeDeriv (iteratedPartialTimeDeriv n Φ)

theorem iteratedPartialTimeDeriv_apply {P : Type} (n : ℕ) (Φ : P × ℝ → ℝ)
    (p : P) (t : ℝ) :
    iteratedPartialTimeDeriv n Φ (p, t) = iteratedDeriv n (fun s => Φ (p, s)) t := by
  induction n generalizing p t with
  | zero => rfl
  | succ n ih =>
    change deriv (fun s => iteratedPartialTimeDeriv n Φ (p, s)) t =
      iteratedDeriv (n + 1) (fun s => Φ (p, s)) t
    rw [iteratedDeriv_succ]
    congr 1
    funext s
    exact ih p s

theorem contDiffAt_iteratedPartialTimeDeriv
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} {x : P × ℝ} (hΦ : ContDiffAt ℝ ∞ Φ x) (n : ℕ) :
    ContDiffAt ℝ ∞ (iteratedPartialTimeDeriv n Φ) x := by
  induction n with
  | zero => exact hΦ
  | succ n ih => exact contDiffAt_partialTimeDeriv ih

/-- The explicit time Taylor sum through degree `n`. -/
def timeTaylorEval {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ) (p : P) (c t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    iteratedDeriv i (fun s => Φ (p, s)) c * (t - c) ^ i / (i ! : ℝ)

@[simp] theorem timeTaylorEval_self {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ) (p : P) (c : ℝ) :
    timeTaylorEval Φ n p c c = Φ (p, c) := by
  simp [timeTaylorEval, Finset.sum_range_succ']

/-- Identification with Mathlib's Taylor polynomial on a nondegenerate
segment, using the actual unrestricted derivatives at the center. -/
theorem timeTaylorEval_eq_taylorWithinEval {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ)
    (p : P) {c t : ℝ} (hct : c ≠ t)
    (hΦc : ContDiffAt ℝ ∞ (fun s => Φ (p, s)) c) :
    timeTaylorEval Φ n p c t = taylorWithinEval (fun s => Φ (p, s)) n (uIcc c t) c t := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hu : UniqueDiffOn ℝ (uIcc c t) := uniqueDiffOn_Icc (by grind)
  rw [iteratedDerivWithin_eq_iteratedDeriv hu (contDiffAt_infty.mp hΦc i) (by simp)]
  simp only [smul_eq_mul]
  ring

/-- The constant is obtained from the actual next time derivative on the
joint compact set. The whole fiber segment must lie in that set. -/
theorem exists_uniform_timeTaylor_remainder_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) {K : Set (P × ℝ)} (hK : IsCompact K)
    (hΦ : ∀ x ∈ K, ContDiffAt ℝ ∞ Φ x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (c t : ℝ),
      (∀ s ∈ uIcc c t, (p, s) ∈ K) →
      |Φ (p, t) - timeTaylorEval Φ n p c t| ≤ C * |t - c| ^ (n + 1) := by
  let D := iteratedPartialTimeDeriv (n + 1) Φ
  have hD : ContinuousOn D K := by
    intro x hx
    exact (contDiffAt_iteratedPartialTimeDeriv (hΦ x hx) (n + 1)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hD
  let M : ℝ := |B|
  let C : ℝ := M / ((n + 1)! : ℝ)
  have hM : 0 ≤ M := abs_nonneg B
  have hfact : 0 < ((n + 1)! : ℝ) := by positivity
  have hC : 0 ≤ C := div_nonneg hM hfact.le
  refine ⟨C, hC, ?_⟩
  intro p c t hseg
  by_cases hct : c = t
  · subst t
    simp
  have hslice : ∀ s ∈ uIcc c t, ContDiffAt ℝ ∞ (fun u => Φ (p, u)) s := by
    intro s hs
    exact (hΦ (p, s) (hseg s hs)).comp s (f := fun u : ℝ => (p, u))
      (contDiffAt_const.prodMk contDiffAt_id)
  have hfn : ContDiffOn ℝ (n + 1) (fun s => Φ (p, s)) (uIcc c t) := by
    intro s hs
    exact (contDiffAt_infty.mp (hslice s hs) (n + 1)).contDiffWithinAt
  obtain ⟨y, hy, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hct hfn
  have hyK : (p, y) ∈ K := hseg y ⟨hy.1.le, hy.2.le⟩
  have hnext : |iteratedDeriv (n + 1) (fun s => Φ (p, s)) y| ≤ M := by
    rw [← iteratedPartialTimeDeriv_apply]
    exact (le_of_eq (Real.norm_eq_abs _).symm).trans ((hB (p, y) hyK).trans (le_abs_self B))
  rw [timeTaylorEval_eq_taylorWithinEval Φ n p hct (hslice c (by simp)), hrem,
    abs_div, abs_mul, abs_pow, abs_of_pos hfact]
  calc
    _ ≤ M * |t - c| ^ (n + 1) / ((n + 1)! : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnext (by positivity)) hfact.le
    _ = C * |t - c| ^ (n + 1) := by dsimp [C]; ring

/-- The critical time scale converts an order `n+1` Taylor remainder into
a bounded frequency-weighted function-value error. -/
theorem frequency_mul_time_power_le_one {r h : ℝ} (hr : 0 < r) (n : ℕ)
    (hh : |h| ≤ r ^ (-(1 / ((n + 1 : ℕ) : ℝ)))) :
    r * |h| ^ (n + 1) ≤ 1 := by
  have he : (r ^ (-(1 / ((n + 1 : ℕ) : ℝ)))) ^ (n + 1) = r⁻¹ := by
    rw [← Real.rpow_mul_natCast hr.le]
    have hexp : -(1 / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = (-1 : ℝ) := by
      field_simp
    rw [hexp, Real.rpow_neg_one]
  calc
    _ ≤ r * (r ^ (-(1 / ((n + 1 : ℕ) : ℝ)))) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg h) hh (n + 1)) hr.le
    _ = 1 := by rw [he, mul_inv_cancel₀ hr.ne']

theorem exists_uniform_frequency_scaled_timeTaylor_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) {K : Set (P × ℝ)} (hK : IsCompact K)
    (hΦ : ∀ x ∈ K, ContDiffAt ℝ ∞ Φ x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : P) (c t r : ℝ), 1 ≤ r →
      (∀ s ∈ uIcc c t, (p, s) ∈ K) →
      |t - c| ≤ r ^ (-(1 / ((n + 1 : ℕ) : ℝ))) →
      r * |Φ (p, t) - timeTaylorEval Φ n p c t| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_timeTaylor_remainder_bound Φ hK hΦ n
  refine ⟨C, hC, ?_⟩
  intro p c t r hr hseg hscale
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  calc
    _ ≤ r * (C * |t - c| ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left (hbound p c t hseg) hrpos.le
    _ = C * (r * |t - c| ^ (n + 1)) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (frequency_mul_time_power_le_one hrpos n hscale) hC
    _ = C := mul_one C

end PlanarNikodym
