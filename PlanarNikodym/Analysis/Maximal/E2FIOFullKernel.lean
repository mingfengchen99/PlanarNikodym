import PlanarNikodym.Analysis.Fourier.TimeFrequencyMixedHessian
import PlanarNikodym.Analysis.Fourier.GlyzSmoothJetCoordinates
import PlanarNikodym.Analysis.Maximal.E2FIOKernelSchur

/-! The actual full time-frequency integral and its input Gram kernel.
The latter is the two-dimensional T*T kernel, without subdividing time
or applying Cauchy across time slices. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate
namespace PlanarNikodym

variable {Q : Type*}

def e2FIOAmplitudeKernel (r : ℝ) (Φ : Q → Plane → ℝ)
    (a : Q × Plane → ℂ) (q : Q) (x : Plane) : ℂ :=
  Complex.exp (((r * Φ q x : ℝ) : ℂ) * Complex.I) * a (q, x)

@[simp] theorem norm_e2FIOAmplitudeKernel (r : ℝ) (Φ : Q → Plane → ℝ)
    (a : Q × Plane → ℂ) (q : Q) (x : Plane) :
    ‖e2FIOAmplitudeKernel r Φ a q x‖ = ‖a (q, x)‖ := by
  simp only [e2FIOAmplitudeKernel, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

def e2FullFIOIntegral (r : ℝ) (Φ : Q → Plane → ℝ)
    (a : Q × Plane → ℂ) (f : Plane → ℂ) (q : Q) : ℂ :=
  ∫ x : Plane, e2FIOAmplitudeKernel r Φ a q x * f x

def e2FIOGramKernel [MeasurableSpace Q] (μ : Measure Q) (r : ℝ)
    (Φ : Q → Plane → ℝ) (a : Q × Plane → ℂ) (x y : Plane) : ℂ :=
  ∫ q, conj (e2FIOAmplitudeKernel r Φ a q x) * e2FIOAmplitudeKernel r Φ a q y ∂μ

theorem e2FIOGramKernel_phase_difference [MeasurableSpace Q] (μ : Measure Q)
    (r : ℝ) (Φ : Q → Plane → ℝ) (a : Q × Plane → ℂ) (x y : Plane) :
    e2FIOGramKernel μ r Φ a x y = ∫ q,
      Complex.exp (((r * (Φ q y - Φ q x) : ℝ) : ℂ) * Complex.I) *
        (conj (a (q, x)) * a (q, y)) ∂μ := by
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [e2FIOAmplitudeKernel, map_mul, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  have he : -(↑(r * Φ q x) * Complex.I) + ↑(r * Φ q y) * Complex.I =
      (↑(r * (Φ q y - Φ q x)) : ℂ) * Complex.I := by
    push_cast
    ring
  calc
    _ = (Complex.exp (-(↑(r * Φ q x) * Complex.I)) *
        Complex.exp (↑(r * Φ q y) * Complex.I)) * (conj (a (q, x)) * a (q, y)) := by ring_nf
    _ = _ := by rw [← Complex.exp_add, he]

def Family.e2SelectedTimeFrequencyPhase {d : ℕ} (G : Family 2 d)
    (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2)) (q : Aux 2) (x : Plane) : ℝ :=
  x.2 * G.γ x.1 (parameterFrame d (v + coordinateInsertion σ q))

theorem Family.e2SelectedTimeFrequencyPhase_contDiff {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2)) :
    ContDiff ℝ ∞ (fun z : Aux 2 × Plane => G.e2SelectedTimeFrequencyPhase σ v z.1 z.2) := by
  exact contDiff_snd.snd.mul (hG.comp (contDiff_snd.fst.prodMk
    ((parameterFrame d).contDiff.comp
      (contDiff_const.add ((coordinateInsertion σ).contDiff.comp contDiff_fst)))))

end PlanarNikodym
