import PlanarNikodym.Analysis.Fourier.PolynomialAmplitudeConeCoordinates
import PlanarNikodym.Analysis.Fourier.ConeOutputDilation

/-! Exact last-stage time-slice representation in the unscaled jet chart.
The phase carries the output dilation `(y₀,y₁) ↦ (y₀,δy₁)` while the
amplitude remains on the fixed chart domain. This is the representation
needed for a frequency-independent amplitude Fourier constant. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem phaseOscillation_jetPolynomial_one_dilated (r δ τ η : ℝ) (y : Aux 2) :
    phaseOscillation (jetPolynomial y) ((2 * Real.pi * r) * η) (δ * τ) =
      planeFourierCharacter (r • coneOutputDilation δ ((y 0, y 1) : Plane)) (η, η * τ) := by
  have he : ((2 * Real.pi * r) * η) * jetPolynomial y (δ * τ) =
      2 * Real.pi * fourierPhase
        (r • coneOutputDilation δ ((y 0, y 1) : Plane)) (η, η * τ) := by
    rw [jetPolynomial_one]
    change (2 * Real.pi * r * η) * (y 0 + y 1 * (δ * τ)) =
      2 * Real.pi * ((r * y 0) * η + (r * (δ * y 1)) * (η * τ))
    ring
  unfold phaseOscillation planeFourierCharacter
  rw [he]

/-- The original time slice in a real cinematic lower-jet chart, with
its actual Taylor amplitude, true input data, and the exact time Jacobian. -/
theorem Family.timeSliceExtension_in_unscaled_linear_chart {d : ℕ} (G : Family 2 d)
    (hm : 2 ≤ d + 2) (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (e : OpenPartialHomeomorph (Aux 2) (Aux 2))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (h : Plane → ℂ) (r : ℝ)
    {δ : ℝ} (hδ : 0 < δ) {y : Aux 2} (hy : y ∈ e.target) :
    timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h
      (2 * Real.pi * r) c δ (parameterFrame d (v + coordinateInsertion σ (e.symm y))) =
      δ • ∫ η : ℝ, ∫ τ : ℝ,
        actualTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          1 (2 * Real.pi * r) c δ
          (parameterFrame d (v + coordinateInsertion σ (e.symm y))) τ η *
        h (c + δ * τ, η) *
        planeFourierCharacter (r • coneOutputDilation δ ((y 0, y 1) : Plane)) (η, η * τ) := by
  rw [timeSliceExtension_eq_taylor _ a h 1 (2 * Real.pi * r) c hδ]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with τ
  have hp : phaseOscillation
      (timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) 1
        (parameterFrame d (v + coordinateInsertion σ (e.symm y))) c)
      ((2 * Real.pi * r) * η) (c + δ * τ) =
      planeFourierCharacter (r • coneOutputDilation δ ((y 0, y 1) : Plane)) (η, η * τ) := by
    unfold phaseOscillation
    rw [G.timeTaylorEval_in_lower_chart hm σ v c e he ha hy, add_sub_cancel_left]
    exact phaseOscillation_jetPolynomial_one_dilated r δ τ η y
  rw [hp]
  ring

end PlanarNikodym
