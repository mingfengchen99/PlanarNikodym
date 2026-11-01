import PlanarNikodym.Analysis.Fourier.GlyzLowerRelativePower

/-! One genuine degree reduction, with its paper exponent and a
frequency-independent constant. Rounded and coarsened depths are exact. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 900000 in
theorem Family.exists_glyz_lower_stage_power {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (k : ℕ) (hk : 0 < k) (hkdim : k + 1 ≤ d + 2) (s : ℕ)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (r : ℝ),
      (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let A := glyzVariableFinalDepth (k + 1) N - s
      let F := glyzVariableFinalDepth k N - s
      (∑ i ∈ Finset.range (2 ^ A),
        ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput A i g) r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1) *
            (1 / (k : ℝ) - 1 / (k + 1 : ℕ)) + ε)) *
          (∑ i ∈ Finset.range (2 ^ F),
            ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput F i g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  obtain ⟨C, hC, hrelative⟩ := G.exists_glyz_lower_relative_power hG ha hc hK hdet has
    k hk hkdim s hp hε hrmin hQ (rmax := rmax)
  let σ : ℝ := (p : ℝ) - glyzCriticalExponent k / 2 - 1
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hσ : 0 ≤ σ := by
    have hcrit : glyzCriticalExponent k ≤ (p : ℝ) := hp
    have htwo : 2 ≤ glyzCriticalExponent k := by
      dsimp [glyzCriticalExponent]
      nlinarith
    dsimp [σ]
    linarith
  let α : ℝ := σ * (1 / (k : ℝ) - 1 / (k + 1 : ℕ)) + ε
  have hfrac : 0 ≤ 1 / (k : ℝ) - 1 / (k + 1 : ℕ) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < k)
    exact_mod_cast Nat.le_succ k
  have hα : 0 ≤ α := add_nonneg (mul_nonneg hσ hfrac) hε.le
  let B := (2 : ℝ) ^ (σ * (s + 1 : ℕ))
  let C' := C * (B + (2 : ℝ) ^ Q)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC' : 0 < C' := mul_pos hC (by positivity)
  have hmainC : C * B ≤ C' := by dsimp [C']; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) Q]
  have herrC : C * (2 : ℝ) ^ Q ≤ C' := by dsimp [C']; nlinarith
  refine ⟨C', hC', fun N r hr hr' g hg hgt hgr => ?_⟩
  let A := glyzVariableFinalDepth (k + 1) N - s
  let F := glyzVariableFinalDepth k N - s
  have hAF : A ≤ F := Nat.sub_le_sub_right
    (glyzVariableFinalDepth_antitone hk (Nat.le_succ k) N) s
  have h := hrelative N A hAF r hr hr' g hg hgt hgr
  have hr0 : 0 < r := (pow_pos (by norm_num : (0 : ℝ) < 2) N).trans_le hr
  have hmain : C * (2 : ℝ) ^ (σ * ((F - A : ℕ) : ℝ) + ε * N) ≤ C' * r ^ α := by
    have hgap := mul_le_mul_of_nonneg_left (glyz_cascade_depth_gap k N s hk) hσ
    calc
      _ ≤ C * (2 : ℝ) ^ (α * N + σ * (s + 1 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp [α]
        dsimp [A, F] at *
        push_cast at *
        nlinarith
      _ = (C * B) * (2 : ℝ) ^ (α * N) := by
        rw [Real.rpow_add (by norm_num)]
        dsimp [B]
        ring
      _ ≤ C' * r ^ α := mul_le_mul hmainC
        (glyz_variable_shell_nonneg_power N hr hα) (by positivity) hC'.le
  have herr : C * (2 : ℝ) ^ (-Q * N) ≤ C' * r ^ (-Q) := by
    calc
      _ ≤ C * ((2 : ℝ) ^ Q * r ^ (-Q)) :=
        mul_le_mul_of_nonneg_left (glyz_variable_shell_decay N hr0 hr' hQ) hC.le
      _ ≤ C' * r ^ (-Q) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right herrC (by positivity)
  exact h.trans (add_le_add
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hmain) _)
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal herr) _))

end PlanarNikodym
