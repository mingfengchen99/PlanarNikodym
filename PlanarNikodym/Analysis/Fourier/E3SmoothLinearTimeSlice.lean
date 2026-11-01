import PlanarNikodym.Analysis.Fourier.UnscaledLinearTimeSlice
import PlanarNikodym.Analysis.Fourier.GlyzSmoothJetCoordinates

/-! Exact Taylor and last-stage slice identities for genuine C∞
phases. The original actual derivative jet and Taylor amplitude are used. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlanarNikodym

theorem Family.e3_timeTaylorEval_eq_lowerJetPolynomial {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (z : Aux (n + 1)) (c t : ℝ)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)) :
    timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n
      (parameterFrame d (v + coordinateInsertion σ z)) c t =
        jetPolynomial (G.lowerCinematicJetMap hm σ c v z) (t - c) := by
  rw [timeTaylorEval_eq_jetPolynomial]
  congr 1
  funext i
  change iteratedDeriv (i : ℕ) (fun s => G.γ s (parameterFrame d (v + coordinateInsertion σ z))) c =
    timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) (i : ℕ)
      (c, parameterFrame d (v + coordinateInsertion σ z))
  exact (timeDerivative_eq_iteratedDeriv_of_contDiff hG i
    (c, parameterFrame d (v + coordinateInsertion σ z))).symm

theorem Family.e3_timeTaylorEval_in_lower_chart {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {y : Aux (n + 1)} (hy : y ∈ e.target) (t : ℝ) :
    timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n
      (parameterFrame d (v + coordinateInsertion σ (e.symm y))) c t =
        jetPolynomial y (t - c) := by
  rw [G.e3_timeTaylorEval_eq_lowerJetPolynomial hm σ v (e.symm y) c t
    hG, ← he, e.right_inv hy]

theorem Family.e3_timeSliceExtension_in_unscaled_linear_chart {d : ℕ} (G : Family 2 d)
    (hm : 2 ≤ d + 2) (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (e : OpenPartialHomeomorph (Aux 2) (Aux 2))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
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
    rw [G.e3_timeTaylorEval_in_lower_chart hm σ v c e he hG hy, add_sub_cancel_left]
    exact phaseOscillation_jetPolynomial_one_dilated r δ τ η y
  rw [hp]
  ring

end PlanarNikodym
