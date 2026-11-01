import PlanarNikodym.Analysis.Fourier.GlyzLowerStagePower
import PlanarNikodym.Analysis.Fourier.GlyzOriginalCoarsePower
import PlanarNikodym.Analysis.Fourier.GlyzPowerErrorComposition

/-! Successive genuine degree reductions in the same original
operator. The full cinematic rank supplies every lower minor; no
analytic estimate is assumed by these final statements. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 1000000 in
theorem Family.exists_glyz_original_cascade_degree_power {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (s j : ℕ) (hj : 2 ≤ j) (hjd : j ≤ d + 1)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (r : ℝ),
      (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let F := glyzVariableFinalDepth j N - s
      (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^ (glyzCascadeExponent (d + 1) j p + ε)) *
          (∑ i ∈ Finset.range (2 ^ F),
            ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput F i g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  let P : ℕ → Prop := fun k => ∀ ε Q : ℝ, 0 < ε → 0 ≤ Q →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (r : ℝ),
      (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let F := glyzVariableFinalDepth k N - s
      (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^ (glyzCascadeExponent (d + 1) k p + ε)) *
          (∑ i ∈ Finset.range (2 ^ F),
            ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput F i g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ)
  have htop : P (d + 1) := by
    intro ε Q hε hQ
    simpa only [glyzCascadeExponent_top (d + 1) (Nat.succ_pos d), Nat.cast_add, Nat.cast_one] using
      G.exists_glyz_original_epsilon_power_coarse hG ha hc hK hdet has s hp hε hrmin hQ
        (rmax := rmax)
  have hstep : ∀ k, k < d + 1 → j ≤ k → P (k + 1) → P k := by
    intro k hkd hjk hprev ε Q hε hQ
    have hk : 0 < k := by omega
    have hpk : glyzCriticalNNExponent k ≤ p := by
      have hh := (glyzCriticalExponent_mono (show k ≤ d + 1 by omega)).trans (show
        glyzCriticalExponent (d + 1) ≤ (p : ℝ) from hp)
      exact_mod_cast hh
    let α := glyzCascadeExponent (d + 1) (k + 1) p + ε / 2
    obtain ⟨C, hC, hCest⟩ := hprev (ε / 2) Q (half_pos hε) hQ
    obtain ⟨D, hD, hDest⟩ := G.exists_glyz_lower_stage_power hG ha hc hK hdet has
      k hk (by omega) s hpk (half_pos hε) hrmin
      (show 0 ≤ Q + |α| by positivity) (rmax := rmax)
    refine ⟨C * (D + 1), mul_pos hC (by positivity), fun N r hr hr' g hg hgt hgr => ?_⟩
    have hr1 : 1 ≤ r := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hr
    have hh := glyz_power_error_compose hC.le hD.le hr1
      (hCest N r hr hr' g hg hgt hgr) (hDest N r hr hr' g hg hgt hgr)
    have he : α + (((p : ℝ) - glyzCriticalExponent k / 2 - 1) *
        (1 / (k : ℝ) - 1 / (k + 1 : ℕ)) + ε / 2) =
        glyzCascadeExponent (d + 1) k p + ε := by
      have hx := glyzCascadeExponent_step (d + 1) k hk p
      dsimp [α]
      linarith
    dsimp only [α] at he
    simpa only [he] using hh
  exact Nat.decreasingInduction' hstep hjd htop ε Q hε hQ

/-- Equation (2.30): after reducing degree d+1 through degree two, the
p-power loss is p/2-(d+1)+epsilon, with arbitrary L1 remainder. -/
theorem Family.exists_glyz_original_cascade_coarse_power {d : ℕ} (G : Family 2 d)
    (hd : 1 ≤ d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (s : ℕ) {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (r : ℝ),
      (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let F := glyzVariableFinalDepth 2 N - s
      (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^ ((p : ℝ) / 2 - (d + 1) + ε)) *
          (∑ i ∈ Finset.range (2 ^ F),
            ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput F i g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  simpa only [glyzCascadeExponent_two, Nat.cast_add, Nat.cast_one] using
    G.exists_glyz_original_cascade_degree_power hG ha hc hK hdet has s 2 le_rfl
      (by omega) hp hε hrmin hQ (rmax := rmax)

end PlanarNikodym
