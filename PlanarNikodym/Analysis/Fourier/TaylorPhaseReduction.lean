import PlanarNikodym.Analysis.Fourier.NormalizedTaylorRemainder
import PlanarNikodym.Analysis.Localization.ScaleTimePartition

/-! Exact absorption of the time Taylor remainder into the amplitude.
On the critical time scale the new amplitudes have uniformly bounded
full parameter/time/frequency jets on fixed compact sets. -/

noncomputable section
open Set
open scoped ContDiff

namespace PlanarNikodym

def criticalTimeScale (n : ℕ) (r : ℝ) : ℝ :=
  r ^ (-(1 / ((n + 1 : ℕ) : ℝ)))

theorem criticalTimeScale_pos (n : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < criticalTimeScale n r := Real.rpow_pos_of_pos hr _

theorem criticalTimeScale_le_one (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    criticalTimeScale n r ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hr (neg_nonpos.mpr (by positivity))

theorem frequency_mul_criticalTimeScale_pow (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r * criticalTimeScale n r ^ (n + 1) = 1 := by
  unfold criticalTimeScale
  rw [← Real.rpow_mul_natCast hr.le]
  have he : -(1 / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = (-1 : ℝ) := by
    field_simp
  rw [he, Real.rpow_neg_one, mul_inv_cancel₀ hr.ne']

/-- Variables are `((parameter, center, normalized time), vertical
frequency)`; the frozen pair is `(frequency * scale^(n+1), scale)`. -/
def taylorPhaseCorrection {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ)
    (q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ) : ℂ :=
  Complex.exp (((q.1.2 * scaledTimeTaylorErrorProfile Φ n (q.1.1, q.2) : ℝ) : ℂ) *
    Complex.I)

theorem contDiff_taylorPhaseCorrection
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ) :
    ContDiff ℝ ∞ (taylorPhaseCorrection Φ n) := by
  have harg : ContDiff ℝ ∞ (fun q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ =>
      (q.1.1, q.2)) := by fun_prop
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_fst.snd.mul
    ((contDiff_scaledTimeTaylorErrorProfile hΦ n).comp harg))).mul contDiff_const).cexp

@[simp] theorem norm_taylorPhaseCorrection {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ)
    (q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ) : ‖taylorPhaseCorrection Φ n q‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- A single constant bounds the actual full fiber jets for every frozen
scale and normalized frequency in the unit square. -/
theorem exists_uniform_taylorPhaseCorrection_jet_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n m : ℕ)
    {K : Set ((P × ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α δ : ℝ), α ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ m (fun y => taylorPhaseCorrection Φ n (y, α, δ)) x‖ ≤ C := by
  have hJ : Continuous (fun q : ((P × ℝ × ℝ) × ℝ) × ℝ × ℝ =>
      iteratedFDeriv ℝ m (fun y => taylorPhaseCorrection Φ n (y, q.2)) q.1) :=
    continuous_iff_continuousAt.mpr (fun _ =>
      (contDiffAt_fiber_iteratedFDeriv m
        (contDiff_taylorPhaseCorrection hΦ n).contDiffAt).continuousAt)
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hJ.continuousOn
  exact ⟨|B|, abs_nonneg _, fun α δ hα hδ x hx =>
    (hB (x, α, δ) ⟨hx, hα, hδ⟩).trans (le_abs_self B)⟩

/-- The correction equals the exponential of the actual remainder,
without deleting a bounded phase error. -/
theorem taylorPhaseCorrection_eq
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ)
    (p : P) (c τ η r δ : ℝ) :
    taylorPhaseCorrection Φ n (((p, c, τ), η), r * δ ^ (n + 1), δ) =
      Complex.exp ((((r * η *
        (Φ (p, c + δ * τ) - timeTaylorEval Φ n p c (c + δ * τ)) : ℝ) : ℂ)) * Complex.I) := by
  unfold taylorPhaseCorrection
  rw [scaledTimeTaylorErrorProfile_eq hΦ]
  congr 2
  push_cast
  ring

theorem phaseOscillation_eq_taylor_mul_correction
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n : ℕ)
    (p : P) (c τ η r δ : ℝ) :
    phaseOscillation (fun t => Φ (p, t)) (r * η) (c + δ * τ) =
      phaseOscillation (timeTaylorEval Φ n p c) (r * η) (c + δ * τ) *
        taylorPhaseCorrection Φ n (((p, c, τ), η), r * δ ^ (n + 1), δ) := by
  rw [taylorPhaseCorrection_eq hΦ, phaseOscillation, phaseOscillation, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Uniform estimates stated directly for the exponential of the true
frequency-weighted remainder at the critical scale. All derivatives are
with respect to parameter, center, normalized time and vertical frequency. -/
theorem exists_uniform_criticalTaylorCorrection_jet_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (n m : ℕ)
    {K : Set ((P × ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun y : (P × ℝ × ℝ) × ℝ =>
        Complex.exp ((((r * y.2 * (Φ (y.1.1, y.1.2.1 + criticalTimeScale n r * y.1.2.2) -
          timeTaylorEval Φ n y.1.1 y.1.2.1
            (y.1.2.1 + criticalTimeScale n r * y.1.2.2)) : ℝ) : ℂ)) * Complex.I)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_taylorPhaseCorrection_jet_bound hΦ n m hK
  refine ⟨C, hC, ?_⟩
  intro r hr x hx
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hδ := criticalTimeScale_pos n hrpos
  have hδ₁ := criticalTimeScale_le_one n hr
  have hα := frequency_mul_criticalTimeScale_pow n hrpos
  have he : (fun y : (P × ℝ × ℝ) × ℝ => taylorPhaseCorrection Φ n
      (y, r * criticalTimeScale n r ^ (n + 1), criticalTimeScale n r)) =
      fun y => Complex.exp ((((r * y.2 *
        (Φ (y.1.1, y.1.2.1 + criticalTimeScale n r * y.1.2.2) -
          timeTaylorEval Φ n y.1.1 y.1.2.1
            (y.1.2.1 + criticalTimeScale n r * y.1.2.2)) : ℝ) : ℂ)) * Complex.I) := by
    funext y
    exact taylorPhaseCorrection_eq hΦ n _ _ _ _ _ _
  rw [← he]
  exact hbound _ _ (by rw [hα]; exact ⟨zero_le_one, le_rfl⟩) ⟨hδ.le, hδ₁⟩ x hx

end PlanarNikodym
