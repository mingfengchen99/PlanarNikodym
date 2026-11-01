import PlanarNikodym.Analysis.Fourier.CinematicTaylorNormalForm
import PlanarNikodym.Analysis.Fourier.LocalTaylorPhaseReduction
import PlanarNikodym.Analysis.Fourier.MicrolocalErrorLp
import PlanarNikodym.Analysis.Fourier.RescaledTaylorAmplitude

/-! Exact reduction of the actual time-slice extension integral. The
Taylor error stays in the amplitude and the time Jacobian is explicit. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

def timeSliceExtension {P : Type} (Φ : P × ℝ → ℝ) (a : P × ℝ × ℝ → ℂ)
    (h : ℝ × ℝ → ℂ) (r c δ : ℝ) (p : P) : ℂ :=
  ∫ η : ℝ, ∫ t : ℝ, phaseOscillation (fun s => Φ (p, s)) (r * η) t *
    a (p, t, η) * (timePartitionWindow ((t - c) / δ) : ℂ) * h (t, η)

def actualTaylorAmplitude {P : Type} (a : P × ℝ × ℝ → ℂ) (Φ : P × ℝ → ℝ)
    (n : ℕ) (r c δ : ℝ) (p : P) (τ η : ℝ) : ℂ :=
  a (p, c + δ * τ, η) * (timePartitionWindow τ : ℂ) *
    frequencyTaylorCorrection Φ n r δ ((p, c, τ), η)

theorem phaseOscillation_eq_taylor_mul_actualCorrection {P : Type}
    (Φ : P × ℝ → ℝ) (n : ℕ) (p : P) (r c δ τ η : ℝ) :
    phaseOscillation (fun s => Φ (p, s)) (r * η) (c + δ * τ) =
      phaseOscillation (timeTaylorEval Φ n p c) (r * η) (c + δ * τ) *
        frequencyTaylorCorrection Φ n r δ ((p, c, τ), η) := by
  unfold phaseOscillation frequencyTaylorCorrection
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_time_affine (F : ℝ → ℂ) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ t, F t) = δ • ∫ τ, F (c + δ * τ) := by
  have he : (∫ τ, F (c + δ * τ)) = δ⁻¹ • ∫ t, F t := by
    rw [Measure.integral_comp_mul_left (fun s => F (c + s)) δ,
      integral_add_left_eq_self, abs_of_pos (inv_pos.mpr hδ)]
  rw [he, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]

theorem timeSliceExtension_eq_taylor {P : Type} (Φ : P × ℝ → ℝ)
    (a : P × ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ) (n : ℕ)
    (r c : ℝ) {δ : ℝ} (hδ : 0 < δ) (p : P) :
    timeSliceExtension Φ a h r c δ p = δ • ∫ η : ℝ, ∫ τ : ℝ,
      phaseOscillation (timeTaylorEval Φ n p c) (r * η) (c + δ * τ) *
        actualTaylorAmplitude a Φ n r c δ p τ η * h (c + δ * τ, η) := by
  unfold timeSliceExtension
  conv_lhs => arg 2; ext η; rw [integral_time_affine _ c hδ]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with η
  apply congrArg (fun z : ℂ => δ • z)
  apply integral_congr_ae
  filter_upwards [] with τ
  rw [phaseOscillation_eq_taylor_mul_actualCorrection Φ n]
  have ht : (c + δ * τ - c) / δ = τ := by field_simp; ring
  rw [ht]
  simp only [actualTaylorAmplitude]
  ring

def polynomialExtension {n : ℕ} (b : Aux (n + 1) → ℝ → ℝ → ℂ)
    (h : ℝ × ℝ → ℂ) (R : ℝ) (w : Aux (n + 1)) : ℂ :=
  ∫ η : ℝ, ∫ τ : ℝ, phaseOscillation (jetPolynomial w) (R * η) τ * b w τ η * h (τ, η)

/-- The lower-degree extension is constructed from the original curve,
the actual inverse coordinates, and the complete Taylor correction. -/
theorem Family.timeSliceExtension_in_scaled_lower_chart {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ)
    (r : ℝ) {δ : ℝ} (hδ : 0 < δ) {w : Aux (n + 1)}
    (hw : w ∈ lowerDegreeDilation n δ hδ.ne' '' e.target) :
    timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h r c δ
      (parameterFrame d (v + coordinateInsertion σ (e.symm ((lowerDegreeDilation n δ hδ.ne').symm w)))) =
      δ • polynomialExtension
        (fun w τ η => actualTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          n r c δ (parameterFrame d (v + coordinateInsertion σ
            (e.symm ((lowerDegreeDilation n δ hδ.ne').symm w)))) τ η)
        (fun x => h (c + δ * x.1, x.2)) (r * δ ^ n) w := by
  rw [timeSliceExtension_eq_taylor _ a h n r c hδ]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with τ
  have hp := G.frequency_timeTaylorEval_in_scaled_lower_chart hm σ v c e he ha hδ.ne' hw r η τ
  simp only [phaseOscillation]
  rw [hp]

/-- The actual partial-Fourier main term is a time-slice extension when
the cutoff is localized by the existing window. All Fourier constants and
the original `r²` prefactor are retained. -/
theorem Family.cutoffPartialExtension_timeSlice {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (L : FrequencyCutoff) (β : ℝ → ℝ) (r c δ : ℝ)
    (f : Plane → ℂ) (q : Parameters 2 d) :
    G.cutoffPartialExtension (fun x => χ x * timePartitionWindow ((x.1 - c) / δ)) L β r f q =
      r ^ 2 • timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
        (fun x => (χ (x.2.1, x.1) : ℂ))
        (fun x => weightedPartialFourierData (fun ξ : Plane => L.bandSymbol 0 ξ * β ξ.2)
          f r x.1 x.2) (2 * Real.pi * r) c δ q := by
  unfold Family.cutoffPartialExtension timeSliceExtension
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, phaseOscillation, oneDimFourierCharacter]
  have he : (2 : ℂ) * Real.pi * r * η * G.γ t q * Complex.I =
      2 * Real.pi * r * G.γ t q * η * Complex.I := by ring
  rw [he]
  ring

end PlanarNikodym
