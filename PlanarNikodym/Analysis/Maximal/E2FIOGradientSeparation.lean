import PlanarNikodym.Analysis.Fourier.GlyzSmoothJetCoordinates
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A genuine uniform local gradient-separation estimate, constructed
from the retained-parameter inverse chart and its actual C¹ inverse.
The constant works simultaneously for all retained parameters in one
open joint neighborhood. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PlanarNikodym
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace P] [CompleteSpace E]

theorem e2_exists_uniform_local_gradient_separation
    {F : P × E → E} (hF : ContDiff ℝ ∞ F) {x : P × E}
    (hi : (fderiv ℝ (fun z => F (x.1, z)) x.2).IsInvertible) :
    ∃ (O : Set (P × E)) (c : ℝ), IsOpen O ∧ x ∈ O ∧ 0 < c ∧
      ∀ (p : P) (u v : E), (p, u) ∈ O → (p, v) ∈ O →
        c * ‖u - v‖ ≤ ‖F (p, u) - F (p, v)‖ := by
  obtain ⟨e, hx, _, he, _, hie, _⟩ := exists_glyz_retained_smooth_chart hF hi
    univ (Filter.univ_mem : univ ∈ 𝓝 x)
  have hey : e x ∈ e.target := e.map_source hx
  have hInv : ContDiffAt ℝ 1 e.symm (e x) := (hie (e x) hey).of_le (by simp)
  obtain ⟨K, S, hS, hLip⟩ := hInv.exists_lipschitzOnWith
  have hn : e.source ∩ e ⁻¹' S ∈ 𝓝 x :=
    inter_mem (e.open_source.mem_nhds hx) ((e.continuousAt hx).preimage_mem_nhds hS)
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hn
  have hK : 0 < (K : ℝ) + 1 := by positivity
  refine ⟨O, ((K : ℝ) + 1)⁻¹, hO, hxO, inv_pos.mpr hK, ?_⟩
  intro p u v hu hv
  have hus := (hOsub hu).1
  have hvs := (hOsub hv).1
  have hb := hLip.dist_le_mul (e (p, u)) (hOsub hu).2 (e (p, v)) (hOsub hv).2
  rw [e.left_inv hus, e.left_inv hvs, he (p, u), he (p, v)] at hb
  have hb' : ‖u - v‖ ≤ (K : ℝ) * ‖F (p, u) - F (p, v)‖ := by
    simpa [dist_eq_norm, Prod.norm_def] using hb
  have hb'' : ‖u - v‖ ≤ ((K : ℝ) + 1) * ‖F (p, u) - F (p, v)‖ := by
    nlinarith [norm_nonneg (F (p, u) - F (p, v))]
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hb'')

end PlanarNikodym
