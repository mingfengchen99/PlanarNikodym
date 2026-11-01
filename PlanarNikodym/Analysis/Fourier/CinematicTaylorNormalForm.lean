import PlanarNikodym.Geometry.CinematicLowerCoordinates
import PlanarNikodym.Analysis.Fourier.LowerDegreePhaseScaling

/-! The actual lower cinematic chart turns the Taylor phase into the
coefficient polynomial. Composing with the anisotropic coefficient
dilation gives its exact lower-degree normalized phase on the true
transformed chart domain. -/

noncomputable section
open Set
open scoped Topology

namespace PlanarNikodym

theorem Family.timeTaylorEval_eq_lowerJetPolynomial {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (z : Aux (n + 1)) (c t : ℝ)
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z))) :
    timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n
      (parameterFrame d (v + coordinateInsertion σ z)) c t =
        jetPolynomial (G.lowerCinematicJetMap hm σ c v z) (t - c) := by
  rw [timeTaylorEval_eq_jetPolynomial]
  congr 1
  funext i
  change iteratedDeriv (i : ℕ) (fun s => G.γ s (parameterFrame d (v + coordinateInsertion σ z))) c =
    timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) (i : ℕ)
      (c, parameterFrame d (v + coordinateInsertion σ z))
  exact (timeDerivative_eq_iteratedDeriv i _ ha).symm

/-- Taylor coefficients are actual jet coordinates on the chart target;
the statement is valid on the genuine nonlinear inverse chart domain. -/
theorem Family.timeTaylorEval_in_lower_chart {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    {y : Aux (n + 1)} (hy : y ∈ e.target) (t : ℝ) :
    timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n
      (parameterFrame d (v + coordinateInsertion σ (e.symm y))) c t =
        jetPolynomial y (t - c) := by
  rw [G.timeTaylorEval_eq_lowerJetPolynomial hm σ v (e.symm y) c t
    (ha (e.symm y) (e.map_target hy)), ← he, e.right_inv hy]

/-- This is the exact anisotropic lower-degree normal form of the actual
Taylor phase, with the true transformed domain and effective frequency. -/
theorem Family.frequency_timeTaylorEval_in_scaled_lower_chart {d n : ℕ} (G : Family 2 d)
    (hm : n + 1 ≤ d + 2) (σ : Fin (n + 1) ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    {δ : ℝ} (hδ : δ ≠ 0) {w : Aux (n + 1)}
    (hw : w ∈ lowerDegreeDilation n δ hδ '' e.target) (r η τ : ℝ) :
    r * η * timeTaylorEval (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) n
      (parameterFrame d (v + coordinateInsertion σ
        (e.symm ((lowerDegreeDilation n δ hδ).symm w)))) c (c + δ * τ) =
      (r * δ ^ n) * η * jetPolynomial w τ := by
  have hy : (lowerDegreeDilation n δ hδ).symm w ∈ e.target := by
    obtain ⟨y, hy, rfl⟩ := hw
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy
  rw [G.timeTaylorEval_in_lower_chart hm σ v c e he ha hy,
    add_sub_cancel_left, jetPolynomial_time_rescale n hδ,
    ContinuousLinearEquiv.apply_symm_apply]
  ring

end PlanarNikodym
