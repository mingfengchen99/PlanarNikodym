import PlanarNikodym.Analysis.Fourier.TaylorJetNondegeneracy
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Actual mixed derivatives of the time/vertical-frequency phase.
The mixed determinant is the vertical frequency times the two-row
time-jet minor. This is a geometric prerequisite for A4.4, not an L²
operator estimate. -/
noncomputable section
open scoped ContDiff
namespace PlanarNikodym

def timeFrequencyPhase {P : Type} (Φ : P × ℝ → ℝ) (p : P) (x : Plane) : ℝ :=
  x.2 * Φ (p, x.1)

theorem fderiv_timeFrequencyPhase_apply {P : Type} (Φ : P × ℝ → ℝ)
    (p : P) (x v : Plane)
    (hΦ : DifferentiableAt ℝ (fun t => Φ (p, t)) x.1) :
    fderiv ℝ (timeFrequencyPhase Φ p) x v =
      x.2 * deriv (fun t => Φ (p, t)) x.1 * v.1 + Φ (p, x.1) * v.2 := by
  have ht := hΦ.hasDerivAt.comp_hasFDerivAt x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
  have hf := (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).mul ht
  have hfe := hf.fderiv
  change fderiv ℝ (fun y : Plane => y.2 * Φ (p, y.1)) x = _ at hfe
  change fderiv ℝ (fun y : Plane => y.2 * Φ (p, y.1)) x v = _
  rw [hfe]
  change x.2 * (deriv (fun t => Φ (p, t)) x.1 * v.1) + Φ (p, x.1) * v.2 = _
  ring

def timeFrequencyMixedMatrix {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P × ℝ → ℝ) (v : Fin 2 → P) (p : P) (t η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderiv ℝ (fun q => fderiv ℝ (timeFrequencyPhase Φ q) (t, η)
    (if i = 0 then (0, 1) else (1, 0))) p (v j)

theorem timeFrequencyMixedMatrix_eq {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (v : Fin 2 → P) (p : P) (t η : ℝ) :
    timeFrequencyMixedMatrix Φ v p t η =
      fun i j => (if i = 0 then 1 else η) * timeJetParameterMatrix Φ 2 v t p i j := by
  have ht (q : P) : DifferentiableAt ℝ (fun s => Φ (q, s)) t :=
    ((hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
  have hD : DifferentiableAt ℝ (fun q => deriv (fun s => Φ (q, s)) t) p := by
    have hT : ContDiffAt ℝ ∞ (iteratedPartialTimeDeriv 1 Φ) (p, t) :=
      contDiffAt_iteratedPartialTimeDeriv hΦ.contDiffAt 1
    have hcomp := hT.comp p (f := fun q : P => (q, t))
      (contDiffAt_id.prodMk contDiffAt_const)
    simpa only [Function.comp_def, iteratedPartialTimeDeriv_apply, iteratedDeriv_one] using
      hcomp.differentiableAt (by simp)
  ext i j
  fin_cases i
  · change fderiv ℝ (fun q => fderiv ℝ (timeFrequencyPhase Φ q) (t, η) (0, 1)) p (v j) =
      1 * timeJetParameterMatrix Φ 2 v t p 0 j
    have he : (fun q => fderiv ℝ (timeFrequencyPhase Φ q) (t, η) (0, 1)) =
        fun q => Φ (q, t) := by
      funext q
      simp [fderiv_timeFrequencyPhase_apply Φ q (t, η) (0, 1) (ht q)]
    rw [he]
    simp [timeJetParameterMatrix, iteratedDeriv_zero]
  · change fderiv ℝ (fun q => fderiv ℝ (timeFrequencyPhase Φ q) (t, η) (1, 0)) p (v j) =
      η * timeJetParameterMatrix Φ 2 v t p 1 j
    have he : (fun q => fderiv ℝ (timeFrequencyPhase Φ q) (t, η) (1, 0)) =
        fun q => η * deriv (fun s => Φ (q, s)) t := by
      funext q
      simp [fderiv_timeFrequencyPhase_apply Φ q (t, η) (1, 0) (ht q)]
    rw [he, fderiv_const_mul hD η]
    simp [timeJetParameterMatrix, iteratedDeriv_one]

theorem det_timeFrequencyMixedMatrix {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (v : Fin 2 → P) (p : P) (t η : ℝ) :
    (timeFrequencyMixedMatrix Φ v p t η).det = η * (timeJetParameterMatrix Φ 2 v t p).det := by
  rw [timeFrequencyMixedMatrix_eq hΦ, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, one_mul]
  ring

theorem abs_det_timeFrequencyMixedMatrix_lower_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (v : Fin 2 → P) (p : P) (t η : ℝ) {b a : ℝ}
    (hb : 0 ≤ b) (hη : a ≤ |η|) (hminor : b ≤ |(timeJetParameterMatrix Φ 2 v t p).det|) :
    a * b ≤ |(timeFrequencyMixedMatrix Φ v p t η).det| := by
  rw [det_timeFrequencyMixedMatrix hΦ, abs_mul]
  exact mul_le_mul hη hminor hb (abs_nonneg _)

end PlanarNikodym
