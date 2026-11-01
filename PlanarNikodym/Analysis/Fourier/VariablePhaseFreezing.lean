import PlanarNikodym.Analysis.Fourier.NormalizedTaylorRemainder
import PlanarNikodym.Analysis.Fourier.TimeSliceExtension

/-! Actual spatial linearization of a variable phase. The quadratic error
is retained exactly, through a smooth normalized integral remainder. The
two parameters controlling its full jets are `lambda * delta^2` and
`delta`; their compact ranges yield bounds uniform in the large frequency. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlanarNikodym

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialLinePhase (Φ : E × ℝ → ℝ) (q : (E × E × ℝ) × ℝ) : ℝ :=
  Φ (q.1.1 + q.2 • q.1.2.1, q.1.2.2)

theorem contDiff_spatialLinePhase {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (spatialLinePhase Φ) := by
  apply hΦ.comp
  fun_prop

def frozenSpatialPhase (Φ : E × ℝ → ℝ) (w z : E) (t : ℝ) : ℝ :=
  fderiv ℝ (fun y => Φ (y, t)) w z

theorem deriv_spatialLinePhase {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (w z : E) (t : ℝ) :
    deriv (fun s : ℝ => spatialLinePhase Φ ((w, z, t), s)) 0 =
      frozenSpatialPhase Φ w z t := by
  have hslice : DifferentiableAt ℝ (fun y : E => Φ (y, t)) w :=
    ((hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableAt
  have hline : HasDerivAt (fun s : ℝ => w + s • z) z 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const z |>.const_add w
  have hs : HasFDerivAt (fun y : E => Φ (y, t))
      (fderiv ℝ (fun y => Φ (y, t)) w) (w + (0 : ℝ) • z) := by
    simpa only [zero_smul, add_zero] using hslice.hasFDerivAt
  have hh := hs.comp_hasDerivAt (0 : ℝ) hline
  have hh' := hh.deriv
  change deriv (fun s : ℝ => Φ (w + s • z, t)) 0 = _ at hh'
  exact hh'

theorem timeTaylorEval_spatialLinePhase_one {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (w z : E) (t δ : ℝ) :
    timeTaylorEval (spatialLinePhase Φ) 1 (w, z, t) 0 δ =
      Φ (w, t) + δ * frozenSpatialPhase Φ w z t := by
  simp only [timeTaylorEval, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedDeriv_zero, iteratedDeriv_one, sub_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one,
    deriv_spatialLinePhase hΦ]
  simp only [spatialLinePhase, zero_smul, add_zero]
  ring

/-- The normalized spatial remainder stays smooth at spatial scale zero. -/
def spatialQuadraticProfile (Φ : E × ℝ → ℝ)
    (q : (E × E × ℝ) × ℝ) : ℝ :=
  timeTaylorIntegralRemainder (spatialLinePhase Φ) 1 (q.1, 0, q.2)

theorem contDiff_spatialQuadraticProfile [FiniteDimensional ℝ E]
    {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (spatialQuadraticProfile Φ) := by
  unfold spatialQuadraticProfile
  apply (contDiff_timeTaylorIntegralRemainder (contDiff_spatialLinePhase hΦ) 1).comp
  fun_prop

theorem spatialPhase_eq_frozen_add_quadratic {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (w z : E) (t δ : ℝ) :
    Φ (w + δ • z, t) = Φ (w, t) + δ * frozenSpatialPhase Φ w z t +
      δ ^ (2 : ℕ) * spatialQuadraticProfile Φ ((w, z, t), δ) := by
  have hh := timeTaylor_remainder_eq_integral (contDiff_spatialLinePhase hΦ)
    1 (w, z, t) 0 δ
  rw [timeTaylorEval_spatialLinePhase_one hΦ] at hh
  change Φ (w + (0 + δ) • z, t) - (Φ (w, t) + (0 + δ) * frozenSpatialPhase Φ w z t) =
    δ ^ (2 : ℕ) * spatialQuadraticProfile Φ ((w, z, t), δ) at hh
  simpa only [zero_add] using (sub_eq_iff_eq_add.mp hh).trans (by ring)

/-- The exponential of the actual spatial Taylor error, including the
vertical frequency. Parameters are `(lambda * delta^2, delta)`. -/
def spatialPhaseCorrection (Φ : E × ℝ → ℝ)
    (q : ((E × E × ℝ) × ℝ) × ℝ × ℝ) : ℂ :=
  Complex.exp (((q.1.2 * q.2.1 * spatialQuadraticProfile Φ (q.1.1, q.2.2) : ℝ) : ℂ) *
    Complex.I)

theorem contDiff_spatialPhaseCorrection [FiniteDimensional ℝ E]
    {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (spatialPhaseCorrection Φ) := by
  have hr : ContDiff ℝ ∞ (fun q : ((E × E × ℝ) × ℝ) × ℝ × ℝ =>
      spatialQuadraticProfile Φ (q.1.1, q.2.2)) :=
    (contDiff_spatialQuadraticProfile hΦ).comp (by fun_prop)
  exact ((Complex.ofRealCLM.contDiff.comp
    ((contDiff_fst.snd.mul contDiff_snd.fst).mul hr)).mul contDiff_const).cexp

@[simp] theorem norm_spatialPhaseCorrection {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E × ℝ → ℝ)
    (q : ((E × E × ℝ) × ℝ) × ℝ × ℝ) : ‖spatialPhaseCorrection Φ q‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Exact freezing; no small remainder is discarded. -/
theorem exp_spatialPhase_eq_frozen_mul_correction {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (w z : E) (t η L δ : ℝ) :
    Complex.exp (((L * η * Φ (w + δ • z, t) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((L * η * Φ (w, t) : ℝ) : ℂ) * Complex.I) *
      Complex.exp ((((L * δ) * η * frozenSpatialPhase Φ w z t : ℝ) : ℂ) * Complex.I) *
      spatialPhaseCorrection Φ (((w, z, t), η), L * δ ^ (2 : ℕ), δ) := by
  rw [spatialPhase_eq_frozen_add_quadratic hΦ]
  unfold spatialPhaseCorrection
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Full mixed jets are uniformly bounded, including the input variables.
The constant precedes both varying scale parameters. -/
theorem exists_uniform_spatialPhaseCorrection_jet_bound [FiniteDimensional ℝ E]
    {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (j : ℕ)
    {K : Set ((E × E × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α δ : ℝ, α ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun y => spatialPhaseCorrection Φ (y, α, δ)) x‖ ≤ C := by
  have hJ : Continuous (fun q : ((E × E × ℝ) × ℝ) × ℝ × ℝ =>
      iteratedFDeriv ℝ j (fun y => spatialPhaseCorrection Φ (y, q.2)) q.1) :=
    continuous_iff_continuousAt.mpr fun _ =>
      (contDiffAt_fiber_iteratedFDeriv j
        (contDiff_spatialPhaseCorrection hΦ).contDiffAt).continuousAt
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hJ.continuousOn
  exact ⟨|B|, abs_nonneg _, fun α δ hα hδ x hx =>
    (hB (x, α, δ) ⟨hx, hα, hδ⟩).trans (le_abs_self B)⟩

/-- At physical radius `rho`, the actual normalized quadratic error is
`rho²/lambda`; the spatial increment is `rho/lambda`. -/
theorem exp_spatialPhase_physical_freezing {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (w z : E) (t η ρ : ℝ) {L : ℝ} (hL : L ≠ 0) :
    Complex.exp (((L * η * Φ (w + (ρ / L) • z, t) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((L * η * Φ (w, t) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((ρ * η * frozenSpatialPhase Φ w z t : ℝ) : ℂ) * Complex.I) *
      spatialPhaseCorrection Φ (((w, z, t), η), ρ ^ (2 : ℕ) / L, ρ / L) := by
  have hh := exp_spatialPhase_eq_frozen_mul_correction hΦ w z t η L (ρ / L)
  have h₁ : L * (ρ / L) = ρ := by field_simp
  have h₂ : L * (ρ / L) ^ (2 : ℕ) = ρ ^ (2 : ℕ) / L := by field_simp
  simpa only [h₁, h₂] using hh

end PlanarNikodym
