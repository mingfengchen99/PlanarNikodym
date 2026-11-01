import PlanarNikodym.Analysis.Fourier.TaylorPhaseReduction
import PlanarNikodym.Analysis.Localization.SmoothCompactExtension

/-! The critical-scale correction bounds only require smoothness near
the actual regular compact set. The phase may be irregular elsewhere. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace PlanarNikodym

/-- The exponential of the true Taylor remainder, in normalized time. -/
def frequencyTaylorCorrection {P : Type} (Φ : P × ℝ → ℝ) (n : ℕ) (r δ : ℝ)
    (x : (P × ℝ × ℝ) × ℝ) : ℂ :=
  Complex.exp ((((r * x.2 *
    (Φ (x.1.1, x.1.2.1 + δ * x.1.2.2) -
      timeTaylorEval Φ n x.1.1 x.1.2.1 (x.1.2.1 + δ * x.1.2.2)) : ℝ) : ℂ)) * Complex.I)

/-- Local agreement of phases preserves the correction on a whole
neighborhood of each normalized parameter point. -/
theorem frequencyTaylorCorrection_eventuallyEq
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ Ψ : P × ℝ → ℝ) {S : Set (P × ℝ)} (hS : IsOpen S) (heq : EqOn Φ Ψ S)
    (n : ℕ) (r δ : ℝ) {x : (P × ℝ × ℝ) × ℝ}
    (hc : (x.1.1, x.1.2.1) ∈ S) (ht : (x.1.1, x.1.2.1 + δ * x.1.2.2) ∈ S) :
    frequencyTaylorCorrection Φ n r δ =ᶠ[𝓝 x] frequencyTaylorCorrection Ψ n r δ := by
  have hcenter : Continuous (fun y : (P × ℝ × ℝ) × ℝ => (y.1.1, y.1.2.1)) := by fun_prop
  have hend : Continuous (fun y : (P × ℝ × ℝ) × ℝ =>
      (y.1.1, y.1.2.1 + δ * y.1.2.2)) := by fun_prop
  filter_upwards [hcenter.continuousAt.preimage_mem_nhds (hS.mem_nhds hc),
    hend.continuousAt.preimage_mem_nhds (hS.mem_nhds ht)] with y hyc hyt
  unfold frequencyTaylorCorrection
  rw [heq hyt, timeTaylorEval_eq_of_eqOn_open Φ Ψ hS heq n _ _ _ hyc]

/-- Actual full correction jets have frequency-independent bounds when
the Taylor center and endpoint belong to the regular compact set. -/
theorem exists_uniform_local_criticalTaylorCorrection_jet_bound
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (Φ : P × ℝ → ℝ) {L S : Set (P × ℝ)} (hL : IsCompact L)
    (hS : IsOpen S) (hLS : L ⊆ S) (hΦ : ∀ x ∈ S, ContDiffAt ℝ ∞ Φ x)
    (n m : ℕ) {K : Set ((P × ℝ × ℝ) × ℝ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x ∈ K,
      (x.1.1, x.1.2.1) ∈ L →
      (x.1.1, x.1.2.1 + criticalTimeScale n r * x.1.2.2) ∈ L →
      ‖iteratedFDeriv ℝ m (frequencyTaylorCorrection Φ n r (criticalTimeScale n r)) x‖ ≤ C := by
  obtain ⟨Ψ, N, hΨ, _, hN, hLN, _, heq⟩ :=
    exists_compact_smooth_extension Φ hL hS hLS hΦ
  obtain ⟨C, hC, hbound⟩ := exists_uniform_criticalTaylorCorrection_jet_bound hΨ n m hK
  refine ⟨C, hC, ?_⟩
  intro r hr x hx hc ht
  have he := frequencyTaylorCorrection_eventuallyEq Φ Ψ hN heq.symm n r
    (criticalTimeScale n r) (hLN hc) (hLN ht)
  rw [(he.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact hbound r hr x hx

end PlanarNikodym
