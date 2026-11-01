import PlanarNikodym.Analysis.Fourier.LowerDegreePhaseScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Pi.Bounds

/-! The critical scale eventually fits every constructed positive
geometric threshold, including the actual Fourier normalization `2πr`. -/
noncomputable section
open Filter
open scoped Topology
namespace PlanarNikodym

theorem tendsto_criticalTimeScale (n : ℕ) : Tendsto (criticalTimeScale n) atTop (𝓝 0) := by
  change Tendsto (fun r : ℝ => r ^ (-(1 / ((n + 1 : ℕ) : ℝ)))) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one] using tendsto_rpow_neg_atTop
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)

theorem exists_criticalTimeScale_threshold (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r → criticalTimeScale n r ≤ ε := by
  have he := (tendsto_criticalTimeScale n).eventually (Iio_mem_nhds hε)
  obtain ⟨R, hR⟩ := eventually_atTop.mp he
  exact ⟨max 1 R, le_max_left _ _, fun r hr => (hR r ((le_max_right _ _).trans hr)).le⟩

theorem exists_Fourier_criticalTimeScale_threshold (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      0 < criticalTimeScale n (2 * Real.pi * r) ∧
      criticalTimeScale n (2 * Real.pi * r) ≤ min 1 ε ∧
      1 ≤ (2 * Real.pi * r) * criticalTimeScale n (2 * Real.pi * r) ^ n := by
  obtain ⟨R, hR, hb⟩ := exists_criticalTimeScale_threshold n (lt_min zero_lt_one hε)
  refine ⟨R, hR, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := hR.trans hr
  have hrr : r ≤ 2 * Real.pi * r := by nlinarith [Real.pi_gt_three]
  have hs : 1 ≤ 2 * Real.pi * r := hr1.trans hrr
  exact ⟨criticalTimeScale_pos n (zero_lt_one.trans_le hs), hb _ (hr.trans hrr),
    critical_effective_frequency_ge_one n hs⟩

end PlanarNikodym
