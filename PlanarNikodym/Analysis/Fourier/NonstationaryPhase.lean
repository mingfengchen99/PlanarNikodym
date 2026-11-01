import PlanarNikodym.Analysis.Fourier.BandOscillatoryRepresentation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! One-dimensional nonstationary phase with an actual recursive amplitude.
The phase derivative is required to be nonzero only on the amplitude's
topological support. No frequency-dependent estimate is an assumption. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PlanarNikodym

def phaseOscillation (φ : ℝ → ℝ) (r t : ℝ) : ℂ :=
  Complex.exp (((r * φ t : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_phaseOscillation (φ : ℝ → ℝ) (r t : ℝ) :
    ‖phaseOscillation φ r t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem contDiff_phaseOscillation {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (r : ℝ) :
    ContDiff ℝ ∞ (phaseOscillation φ r) := by
  unfold phaseOscillation
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ)).mul contDiff_const).cexp

theorem hasDerivAt_phaseOscillation {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (r t : ℝ) : HasDerivAt (phaseOscillation φ r)
      (((r : ℂ) * Complex.I) * ((deriv φ t : ℝ) : ℂ) * phaseOscillation φ r t) t := by
  have h := (((hφ.differentiable (by simp) t).hasDerivAt.const_mul r).ofReal_comp.mul_const
    Complex.I).cexp
  convert h using 1
  · rfl
  · simp only [phaseOscillation, Complex.ofReal_mul]
    ring

theorem contDiffAt_phaseOscillation {φ : ℝ → ℝ} {t : ℝ}
    (hφ : ContDiffAt ℝ ∞ φ t) (r : ℝ) :
    ContDiffAt ℝ ∞ (phaseOscillation φ r) t := by
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp t (contDiffAt_const.mul hφ)).mul
    contDiffAt_const).cexp

theorem hasDerivAt_phaseOscillation_of_contDiffAt {φ : ℝ → ℝ} {t : ℝ}
    (hφ : ContDiffAt ℝ ∞ φ t) (r : ℝ) :
    HasDerivAt (phaseOscillation φ r)
      (((r : ℂ) * Complex.I) * ((deriv φ t : ℝ) : ℂ) * phaseOscillation φ r t) t := by
  have h := (((hφ.differentiableAt (by simp)).hasDerivAt.const_mul r).ofReal_comp.mul_const
    Complex.I).cexp
  convert h using 1
  · rfl
  · simp only [phaseOscillation, Complex.ofReal_mul]
    ring

/-- A smooth multiplier supported where the second factor is locally smooth
gives a globally smooth product, even for an arbitrary extension elsewhere. -/
theorem contDiff_mul_of_contDiffAt_tsupport {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ∀ t ∈ tsupport f, ContDiffAt ℝ ∞ g t) :
    ContDiff ℝ ∞ (fun t => f t * g t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t ∈ tsupport f
  · exact hf.contDiffAt.mul (hg t ht)
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with s hs
    simp only [Pi.zero_apply] at hs
    simp only [hs, zero_mul]

/-- Division is globally defined; it is smooth because zeros of the phase
derivative are disjoint from the topological support of the numerator. -/
def nonstationaryQuotient (φ : ℝ → ℝ) (χ : ℝ → ℂ) (t : ℝ) : ℂ :=
  χ t / ((deriv φ t : ℝ) : ℂ)

theorem tsupport_nonstationaryQuotient_subset (φ : ℝ → ℝ) (χ : ℝ → ℂ) :
    tsupport (nonstationaryQuotient φ χ) ⊆ tsupport χ := by
  change tsupport (fun t : ℝ => χ t / ((deriv φ t : ℝ) : ℂ)) ⊆ tsupport χ
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

theorem hasCompactSupport_nonstationaryQuotient (φ : ℝ → ℝ) {χ : ℝ → ℂ}
    (hc : HasCompactSupport χ) : HasCompactSupport (nonstationaryQuotient φ χ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_nonstationaryQuotient_subset φ χ)

theorem contDiff_nonstationaryQuotient {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) :
    ContDiff ℝ ∞ (nonstationaryQuotient φ χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t ∈ tsupport χ
  · have hdφ : ContDiffAt ℝ ∞ (deriv φ) t := (hφ t ht).derivWithin (by simp)
    change ContDiffAt ℝ ∞ (fun s => χ s / ((deriv φ s : ℝ) : ℂ)) t
    simp only [div_eq_mul_inv]
    exact hχ.contDiffAt.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp t hdφ).inv
        (by
          change ((deriv φ t : ℝ) : ℂ) ≠ 0
          exact_mod_cast hne t ht))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with s hs
    simp only [Pi.zero_apply] at hs
    simp only [nonstationaryQuotient, hs, zero_div]

/-- The actual one-step integration-by-parts amplitude. -/
def nonstationaryTransfer (φ : ℝ → ℝ) (χ : ℝ → ℂ) (t : ℝ) : ℂ :=
  -deriv (nonstationaryQuotient φ χ) t

theorem tsupport_nonstationaryTransfer_subset (φ : ℝ → ℝ) (χ : ℝ → ℂ) :
    tsupport (nonstationaryTransfer φ χ) ⊆ tsupport χ := by
  calc
    _ = tsupport (deriv (nonstationaryQuotient φ χ)) := by
      exact tsupport_neg (deriv (nonstationaryQuotient φ χ))
    _ ⊆ tsupport (nonstationaryQuotient φ χ) := tsupport_deriv_subset
    _ ⊆ _ := tsupport_nonstationaryQuotient_subset φ χ

theorem hasCompactSupport_nonstationaryTransfer (φ : ℝ → ℝ) {χ : ℝ → ℂ}
    (hc : HasCompactSupport χ) : HasCompactSupport (nonstationaryTransfer φ χ) :=
  (hasCompactSupport_nonstationaryQuotient φ hc).deriv.neg

theorem contDiff_nonstationaryTransfer {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) :
    ContDiff ℝ ∞ (nonstationaryTransfer φ χ) :=
  (contDiff_infty_iff_deriv.mp (contDiff_nonstationaryQuotient hφ hχ hne)).2.neg

theorem integrable_phaseOscillation_mul {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (r : ℝ) : Integrable (fun t => phaseOscillation φ r t * χ t) := by
  have hs := contDiff_mul_of_contDiffAt_tsupport hχ
    (fun t ht => contDiffAt_phaseOscillation (hφ t ht) r)
  simpa only [mul_comm] using hs.continuous.integrable_of_hasCompactSupport hc.mul_right

/-- One integration by parts, including the zero-frequency identity. -/
theorem phaseOscillation_integral_mul_eq_transfer {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) (r : ℝ) :
    ((r : ℂ) * Complex.I) * (∫ t : ℝ, phaseOscillation φ r t * χ t) =
      ∫ t : ℝ, phaseOscillation φ r t * nonstationaryTransfer φ χ t := by
  let q := nonstationaryQuotient φ χ
  let v := phaseOscillation φ r
  have hq : ContDiff ℝ ∞ q := contDiff_nonstationaryQuotient hφ hχ hne
  have hcq : HasCompactSupport q := hasCompactSupport_nonstationaryQuotient φ hc
  have hdq : ContDiff ℝ ∞ (deriv q) := (contDiff_infty_iff_deriv.mp hq).2
  have hv : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ v t :=
    fun t ht => contDiffAt_phaseOscillation (hφ t ht) r
  have hqv : ContDiff ℝ ∞ (fun t => q t * v t) :=
    contDiff_mul_of_contDiffAt_tsupport hq
      (fun t ht => hv t (tsupport_nonstationaryQuotient_subset φ χ ht))
  have hdqv : ContDiff ℝ ∞ (fun t => deriv q t * v t) :=
    contDiff_mul_of_contDiffAt_tsupport hdq (fun t ht => hv t
      (tsupport_nonstationaryQuotient_subset φ χ (tsupport_deriv_subset ht)))
  have hqdv : ContDiff ℝ ∞ (fun t => q t * deriv v t) :=
    contDiff_mul_of_contDiffAt_tsupport hq (fun t ht =>
      (hv t (tsupport_nonstationaryQuotient_subset φ χ ht)).derivWithin (by simp))
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := q) (u' := deriv q) (v := v) (v' := deriv v)
    (fun t _ => (hq.differentiable (by simp) t).hasDerivAt)
    (fun t ht => (hv t (tsupport_nonstationaryQuotient_subset φ χ ht)).differentiableAt
      (by simp) |>.hasDerivAt)
    (hqdv.continuous.integrable_of_hasCompactSupport hcq.mul_right)
    (hdqv.continuous.integrable_of_hasCompactSupport hcq.deriv.mul_right)
    (hqv.continuous.integrable_of_hasCompactSupport hcq.mul_right)
  have he : (fun t : ℝ => q t * deriv v t) =
      (fun t : ℝ => ((r : ℂ) * Complex.I) * (phaseOscillation φ r t * χ t)) := by
    funext t
    by_cases ht : χ t = 0
    · simp [q, nonstationaryQuotient, ht]
    · rw [show deriv v t = ((r : ℂ) * Complex.I) * ((deriv φ t : ℝ) : ℂ) *
        phaseOscillation φ r t from
          (hasDerivAt_phaseOscillation_of_contDiffAt (hφ t (subset_tsupport χ ht)) r).deriv]
      have ht' : ((deriv φ t : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hne t (subset_tsupport χ ht)
      dsimp [q, nonstationaryQuotient]
      field_simp [ht']
  rw [he, integral_const_mul] at hibp
  rw [hibp]
  simp only [nonstationaryTransfer, q, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

/-- The transfer amplitudes depend only on the initial amplitude and phase,
and are independent of the oscillation frequency. -/
def nonstationaryAmplitude (φ : ℝ → ℝ) (χ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => χ
  | n + 1 => nonstationaryTransfer φ (nonstationaryAmplitude φ χ n)

theorem tsupport_nonstationaryAmplitude_subset (φ : ℝ → ℝ) (χ : ℝ → ℂ) (n : ℕ) :
    tsupport (nonstationaryAmplitude φ χ n) ⊆ tsupport χ := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact (tsupport_nonstationaryTransfer_subset φ _).trans ih

theorem hasCompactSupport_nonstationaryAmplitude (φ : ℝ → ℝ) {χ : ℝ → ℂ}
    (hc : HasCompactSupport χ) (n : ℕ) :
    HasCompactSupport (nonstationaryAmplitude φ χ n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact hasCompactSupport_nonstationaryTransfer φ ih

theorem contDiff_nonstationaryAmplitude {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) (n : ℕ) :
    ContDiff ℝ ∞ (nonstationaryAmplitude φ χ n) := by
  induction n with
  | zero => exact hχ
  | succ n ih =>
    exact contDiff_nonstationaryTransfer
      (fun t ht => hφ t (tsupport_nonstationaryAmplitude_subset φ χ n ht)) ih
      (fun t ht => hne t (tsupport_nonstationaryAmplitude_subset φ χ n ht))

theorem integrable_nonstationaryAmplitude {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) (n : ℕ) :
    Integrable (nonstationaryAmplitude φ χ n) :=
  (contDiff_nonstationaryAmplitude hφ hχ hne n).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_nonstationaryAmplitude φ hc n)

theorem phaseOscillation_integral_eq_inv_mul_transfer {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    (∫ t : ℝ, phaseOscillation φ r t * χ t) =
      ((r : ℂ) * Complex.I)⁻¹ *
        ∫ t : ℝ, phaseOscillation φ r t * nonstationaryTransfer φ χ t := by
  have hcoef : (r : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hr) Complex.I_ne_zero
  apply mul_left_cancel₀ hcoef
  rw [phaseOscillation_integral_mul_eq_transfer hφ hχ hc hne r,
    mul_inv_cancel_left₀ hcoef]

/-- Repeated integration by parts with actual recursively constructed smooth
compact amplitudes and no global nonvanishing assumption on the phase. -/
theorem phaseOscillation_integral_eq_iterated_transfer {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    (∫ t : ℝ, phaseOscillation φ r t * χ t) =
      (((r : ℂ) * Complex.I)⁻¹) ^ n *
        ∫ t : ℝ, phaseOscillation φ r t * nonstationaryAmplitude φ χ n t := by
  induction n with
  | zero => simp [nonstationaryAmplitude]
  | succ n ih =>
    rw [ih, phaseOscillation_integral_eq_inv_mul_transfer
      (fun t ht => hφ t (tsupport_nonstationaryAmplitude_subset φ χ n ht))
      (contDiff_nonstationaryAmplitude hφ hχ hne n)
      (hasCompactSupport_nonstationaryAmplitude φ hc n)
      (fun t ht => hne t (tsupport_nonstationaryAmplitude_subset φ χ n ht)) hr]
    simp only [nonstationaryAmplitude, pow_succ, mul_assoc]

/-- Arbitrary-order nonstationary decay. The integral on the right depends
only on the phase, original amplitude and number of integrations by parts. -/
theorem norm_phaseOscillation_integral_le {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) {r : ℝ} (hr : r ≠ 0) (n : ℕ) :
    ‖∫ t : ℝ, phaseOscillation φ r t * χ t‖ ≤
      (|r|⁻¹) ^ n * ∫ t : ℝ, ‖nonstationaryAmplitude φ χ n t‖ := by
  rw [phaseOscillation_integral_eq_iterated_transfer hφ hχ hc hne hr n]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one]
  have h := norm_integral_le_integral_norm (μ := volume)
    (fun t : ℝ => phaseOscillation φ r t * nonstationaryAmplitude φ χ n t)
  simpa only [norm_mul, norm_phaseOscillation, one_mul] using
    (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (|r|⁻¹) ^ n))

theorem exists_nonstationary_decay_constant {φ : ℝ → ℝ} {χ : ℝ → ℂ}
    (hφ : ∀ t ∈ tsupport χ, ContDiffAt ℝ ∞ φ t) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hne : ∀ t ∈ tsupport χ, deriv φ t ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, r ≠ 0 →
      ‖∫ t : ℝ, phaseOscillation φ r t * χ t‖ ≤ C * (|r|⁻¹) ^ n := by
  refine ⟨∫ t : ℝ, ‖nonstationaryAmplitude φ χ n t‖,
    integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro r hr
  simpa only [mul_comm] using norm_phaseOscillation_integral_le hφ hχ hc hne hr n

end PlanarNikodym
