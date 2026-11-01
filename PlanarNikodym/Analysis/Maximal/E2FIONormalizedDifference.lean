import PlanarNikodym.Analysis.Maximal.E2FIOFullKernel
import PlanarNikodym.Analysis.Fourier.NormalizedTaylorRemainder

/-! The actual normalized phase difference extends smoothly through
the diagonal. This is the joint Hadamard formula used before applying
uniform nonstationary phase to the full two-dimensional input kernel. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

def e2FIOPathPhase (Φ : Q × Plane → ℝ) (z : ((Q × Plane) × Plane) × ℝ) : ℝ :=
  Φ (z.1.1.1, z.1.1.2 + z.2 • z.1.2)

def e2FIONormalizedDifference (Φ : Q × Plane → ℝ)
    (z : ((Q × Plane) × Plane) × ℝ) : ℝ :=
  timeTaylorIntegralRemainder (e2FIOPathPhase Φ) 0 (z.1, 0, z.2)

omit [FiniteDimensional ℝ Q] in
theorem e2FIOPathPhase_contDiff {Φ : Q × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (e2FIOPathPhase Φ) := by
  exact hΦ.comp (contDiff_fst.fst.fst.prodMk
    (contDiff_fst.fst.snd.add (contDiff_snd.smul contDiff_fst.snd)))

theorem e2FIONormalizedDifference_contDiff {Φ : Q × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (e2FIONormalizedDifference Φ) := by
  exact (contDiff_timeTaylorIntegralRemainder (e2FIOPathPhase_contDiff hΦ) 0).comp
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

omit [FiniteDimensional ℝ Q] in
theorem e2FIO_phase_difference_exact {Φ : Q × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (q : Q) (x vdir : Plane) (h : ℝ) :
    Φ (q, x + h • vdir) - Φ (q, x) =
      h * e2FIONormalizedDifference Φ (((q, x), vdir), h) := by
  have hh := timeTaylor_remainder_eq_integral (e2FIOPathPhase_contDiff hΦ) 0
    ((q, x), vdir) 0 h
  simpa [e2FIOPathPhase, e2FIONormalizedDifference, timeTaylorEval,
    iteratedPartialTimeDeriv] using hh

omit [FiniteDimensional ℝ Q] in
theorem e2FIONormalizedDifference_zero {Φ : Q × Plane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (q : Q) (x vdir : Plane) :
    e2FIONormalizedDifference Φ (((q, x), vdir), 0) =
      fderiv ℝ (fun y : Plane => Φ (q, y)) x vdir := by
  have hd : HasDerivAt (fun s : ℝ => Φ (q, x + s • vdir))
      (fderiv ℝ (fun y : Plane => Φ (q, y)) x vdir) 0 := by
    have hp : HasDerivAt (fun s : ℝ => x + s • vdir) vdir 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const vdir).const_add x
    have hslice : DifferentiableAt ℝ (fun y : Plane => Φ (q, y)) x :=
      ((hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
    have hsp : HasFDerivAt (fun y : Plane => Φ (q, y))
        (fderiv ℝ (fun y : Plane => Φ (q, y)) x) (x + (0 : ℝ) • vdir) := by
      simpa only [zero_smul, add_zero] using hslice.hasFDerivAt
    exact hsp.comp_hasDerivAt 0 hp
  simp only [e2FIONormalizedDifference, timeTaylorIntegralRemainder, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, one_mul, zero_mul, add_zero,
    iteratedPartialTimeDeriv_apply, Nat.zero_add, iteratedDeriv_one]
  change (∫ s in (0 : ℝ)..1, deriv (fun t : ℝ => Φ (q, x + t • vdir)) 0) = _
  rw [hd.deriv]
  simp

end PlanarNikodym
