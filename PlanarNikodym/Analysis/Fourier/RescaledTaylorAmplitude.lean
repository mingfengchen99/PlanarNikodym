import PlanarNikodym.Analysis.Fourier.TaylorPhaseReduction

/-! Uniform full jets of the actual rescaled amplitude, after exact
absorption of the Taylor error. Both scale parameters vary in a fixed
compact square, which gives constants independent of frequency. -/

noncomputable section
open Set
open scoped ContDiff

namespace PlanarNikodym

/-- An original amplitude `a(parameter,time,frequency)` is pulled back
by `time = center + scale * normalizedTime`, localized by the fixed
window, and multiplied by the exact phase correction. -/
def rescaledTaylorAmplitude {P : Type} (a : P × ℝ × ℝ → ℂ)
    (Φ : P × ℝ → ℝ) (n : ℕ) (q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ) : ℂ :=
  a (q.1.1.1, q.1.1.2.1 + q.2.2 * q.1.1.2.2, q.1.2) *
    (timePartitionWindow q.1.1.2.2 : ℂ) * taylorPhaseCorrection Φ n q

theorem contDiff_rescaledTaylorAmplitude
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a : P × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ) :
    ContDiff ℝ ∞ (rescaledTaylorAmplitude a Φ n) := by
  have harg : ContDiff ℝ ∞ (fun q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ =>
      (q.1.1.1, q.1.1.2.1 + q.2.2 * q.1.1.2.2, q.1.2)) := by fun_prop
  exact ((ha.comp harg).mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_timePartitionWindow.comp contDiff_fst.fst.snd.snd))).mul
      (contDiff_taylorPhaseCorrection hΦ n)

theorem rescaledTaylorAmplitude_eq_zero_of_time
    {P : Type} (a : P × ℝ × ℝ → ℂ) (Φ : P × ℝ → ℝ) (n : ℕ)
    (q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ)
    (ht : q.1.1.2.2 ≤ -1 ∨ 1 ≤ q.1.1.2.2) :
    rescaledTaylorAmplitude a Φ n q = 0 := by
  simp only [rescaledTaylorAmplitude, timePartitionWindow_eq_zero ht, Complex.ofReal_zero,
    mul_zero, zero_mul]

/-- Uniform bounds for every complete mixed jet, including normalized
time and frequency derivatives, of the rescaled amplitude. -/
theorem exists_uniform_rescaledTaylorAmplitude_jet_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a : P × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n m : ℕ)
    {K : Set ((P × ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α δ : ℝ), α ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ m (fun y => rescaledTaylorAmplitude a Φ n (y, α, δ)) x‖ ≤ C := by
  have hJ : Continuous (fun q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ =>
      iteratedFDeriv ℝ m (fun y => rescaledTaylorAmplitude a Φ n (y, q.2)) q.1) :=
    continuous_iff_continuousAt.mpr (fun _ =>
      (contDiffAt_fiber_iteratedFDeriv m
        (contDiff_rescaledTaylorAmplitude ha hΦ n).contDiffAt).continuousAt)
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hJ.continuousOn
  exact ⟨|B|, abs_nonneg _, fun α δ hα hδ x hx =>
    (hB (x, α, δ) ⟨hx, hα, hδ⟩).trans (le_abs_self B)⟩

theorem exists_uniform_critical_rescaledTaylorAmplitude_jet_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a : P × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n m : ℕ)
    {K : Set ((P × ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun y => rescaledTaylorAmplitude a Φ n
        (y, r * criticalTimeScale n r ^ (n + 1), criticalTimeScale n r)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_rescaledTaylorAmplitude_jet_bound ha hΦ n m hK
  refine ⟨C, hC, ?_⟩
  intro r hr x hx
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  apply hbound _ _ ?_ ⟨(criticalTimeScale_pos n hrpos).le, criticalTimeScale_le_one n hr⟩ x hx
  rw [frequency_mul_criticalTimeScale_pow n hrpos]
  exact ⟨zero_le_one, le_rfl⟩

/-- The original integrand equals the polynomial-phase integrand with
this rescaled amplitude, pointwise and exactly. -/
theorem phase_mul_amplitude_eq_taylor_rescaled
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P × ℝ × ℝ → ℂ) {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (n : ℕ) (p : P) (c τ η r δ : ℝ) :
    phaseOscillation (fun t => Φ (p, t)) (r * η) (c + δ * τ) *
      a (p, c + δ * τ, η) * (timePartitionWindow τ : ℂ) =
      phaseOscillation (timeTaylorEval Φ n p c) (r * η) (c + δ * τ) *
        rescaledTaylorAmplitude a Φ n (((p, c, τ), η), r * δ ^ (n + 1), δ) := by
  rw [phaseOscillation_eq_taylor_mul_correction hΦ n]
  simp only [rescaledTaylorAmplitude]
  ring

end PlanarNikodym
