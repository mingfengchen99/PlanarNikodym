import PlanarNikodym.Geometry.MovingCinematicCoordinates
import PlanarNikodym.Analysis.Fourier.ParametricChartBounds

/-! A compact joint chart and every uniform constant are constructed
from the original cinematic determinant. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

theorem Family.exists_uniform_movingLowerJet_chart {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v))
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0) (m : ℕ) (hm : m ≤ d + 2) :
    ∃ (σ : Fin m ↪ Fin (d + 2))
      (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
        ((ℝ × Aux (d + 2)) × Aux m)) (K L : Set ((ℝ × Aux (d + 2)) × Aux m)),
      IsCompact K ∧ IsCompact L ∧ ((t, v), (0 : Aux m)) ∈ interior K ∧
      K ⊆ e.source ∧ L = e '' K ∧ L ⊆ e.target ∧
      (∀ x, e x = (x.1, G.movingLowerJetMap hm σ x)) ∧
      AnalyticOnNhd ℝ e e.source ∧ AnalyticOnNhd ℝ e.symm e.target ∧
      (∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ x ∈ K,
        b ≤ |fiberChartJacobian e x| ∧ |fiberChartJacobian e x| ≤ C) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        (∀ x ∈ K, ‖iteratedFDeriv ℝ j e x‖ ≤ C) ∧
        ∀ y ∈ L, ‖iteratedFDeriv ℝ j e.symm y‖ ≤ C) ∧
      ∀ x ∈ e.source, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
        (x.1.1, parameterFrame d (x.1.2 + coordinateInsertion σ x.2)) := by
  obtain ⟨σ, e, hx, _, he, hea, hei, _, hreg⟩ :=
    G.exists_movingLowerJet_analytic_chart ha hdet m hm univ univ_mem
  obtain ⟨K, hK, hxK, hKS⟩ := exists_compact_subset e.open_source hx
  have hL : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKS)
  have hLT : e '' K ⊆ e.target := e.image_source_subset.trans' (image_mono hKS)
  have hfirst : ∀ x, (e x).1 = x.1 := by intro x; rw [he]
  refine ⟨σ, e, K, e '' K, hK, hL, hxK, hKS, rfl, hLT, he, hea, hei,
    exists_uniform_fiberChartJacobian_bounds e hfirst hea hei hK hKS, ?_, hreg⟩
  intro j
  exact exists_uniform_joint_chart_jet_bounds e hea hei hK hKS hL hLT j

end PlanarNikodym
