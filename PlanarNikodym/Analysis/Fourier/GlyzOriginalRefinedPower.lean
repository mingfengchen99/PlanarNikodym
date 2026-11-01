import PlanarNikodym.Analysis.Fourier.GlyzOriginalEpsilonPower

/-! A fixed additional refinement of the actual original-operator
estimate. Its only cost is the frequency-independent counting factor
2^(q(p-1)); the frequency exponent and arbitrary decay order persist. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace PlanarNikodym

set_option maxHeartbeats 600000 in
/-- The finest dyadic depth may be increased by any fixed q, chosen
before the final constant and before every frequency and input. -/
theorem Family.exists_glyz_original_epsilon_power_refined {d : ℕ} (G : Family 2 d)
    (hG : ContDiff ℝ ∞ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2))
    {a : Parameters 2 d × Plane → ℂ} (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {K : Set (ℝ × Parameters 2 d)} (hK : IsCompact K)
    (hdet : ∀ x ∈ K, G.cinematicDet x ≠ 0)
    (has : ∀ x t η, a (x, t, η) ≠ 0 → (t, x) ∈ K)
    (q : ℕ) {p : ℝ≥0} (hp : glyzCriticalNNExponent (d + 1) ≤ p)
    {ε rmin rmax Q : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (r : ℝ),
      (2 : ℝ) ^ N ≤ r → r ≤ (2 : ℝ) ^ (N + 1) →
      ∀ g : Plane → ℂ, Integrable g →
      Function.support g ⊆ {y | y.1 ∈ Ico (0 : ℝ) 1} →
      Function.support g ⊆ {y | y.2 ∈ Icc rmin rmax} →
      let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
      let F := glyzVariableFinalDepth (d + 1) N + q
      (∫⁻ x, ‖glyzRawExtension Φ a g r x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * r ^
          (((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε)) *
          (∑ i ∈ Finset.range (2 ^ F),
            ∫⁻ x, ‖glyzRawExtension Φ a (glyzDyadicInput F i g) r x‖ₑ ^ (p : ℝ)) +
        ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
  obtain ⟨C, hC, hmain⟩ :=
    G.exists_glyz_original_epsilon_power hG ha hc hK hdet has hp hε hrmin hQ
      (rmax := rmax)
  have hp1 : (1 : ℝ) ≤ p :=
    (one_le_glyzCriticalNNExponent (by omega : 0 < d + 1)).trans hp
  let B : ℝ := (2 : ℝ) ^ ((q : ℝ) * ((p : ℝ) - 1))
  have hB : 1 ≤ B :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr hp1))
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hCC : C ≤ C * B := le_mul_of_one_le_right hC.le hB
  refine ⟨C * B, mul_pos hC hB0, fun N r hr hr' g hg hgt hgr => ?_⟩
  let Φ := fun x : Parameters 2 d × ℝ => G.γ x.2 x.1
  let H := glyzRawKernel Φ a r
  let F := glyzVariableFinalDepth (d + 1) N
  let s := ((p : ℝ) - glyzCriticalExponent (d + 1) / 2 - 1) / (d + 1) + ε
  have hr0 : 0 < r := (pow_pos (by norm_num : (0 : ℝ) < 2) N).trans_le hr
  have hΦ : ContDiff ℝ ∞ Φ := hG.comp (contDiff_snd.prodMk contDiff_fst)
  have hH : ContDiff ℝ ∞ H := contDiff_glyzRawKernel hΦ ha r
  have hcH : HasCompactSupport H := hasCompactSupport_glyzRawKernel Φ hc r
  have hbase : (∫⁻ x, ‖∫ y, g y * H (x, y)‖ₑ ^ (p : ℝ)) ≤
      ENNReal.ofReal (C * r ^ s) * glyzDyadicKernelEnergy volume H g F p +
      ENNReal.ofReal (C * r ^ (-Q)) * (∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ) := by
    simpa only [glyzRawExtension_eq_compactKernel hΦ ha hc hg r,
      glyzRawExtension_dyadicInput_eq_piece hΦ ha hc hg r,
      glyzDyadicKernelEnergy, H, Φ, F, s] using hmain N r hr hr' g hg hgt hgr
  have href : glyzDyadicKernelEnergy volume H g F p ≤
      ENNReal.ofReal B * glyzDyadicKernelEnergy volume H g (F + q) p := by
    simpa only [Nat.add_sub_cancel_left, glyz_ennreal_dyadic_count, B] using
      glyzDyadicKernelEnergy_trivial_refine volume hH hcH hg hgt F (F + q)
        (Nat.le_add_right _ _) hp1
  have hcoeff : ENNReal.ofReal (C * r ^ s) * ENNReal.ofReal B =
      ENNReal.ofReal ((C * B) * r ^ s) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg hr0.le _))]
    congr 1
    ring
  have herr : ENNReal.ofReal (C * r ^ (-Q)) ≤ ENNReal.ofReal ((C * B) * r ^ (-Q)) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hr0.le _))
  have h := hbase.trans (add_le_add
    (mul_le_mul_right href (ENNReal.ofReal (C * r ^ s)))
    (mul_le_mul_left herr ((∫⁻ y, ‖g y‖ₑ) ^ (p : ℝ))))
  rw [← mul_assoc, hcoeff] at h
  simpa only [glyzRawExtension_eq_compactKernel hΦ ha hc hg r,
    glyzRawExtension_dyadicInput_eq_piece hΦ ha hc hg r,
    glyzDyadicKernelEnergy, H, Φ, F, s] using h

end PlanarNikodym
