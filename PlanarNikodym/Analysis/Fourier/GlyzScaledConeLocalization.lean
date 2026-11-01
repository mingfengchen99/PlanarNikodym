import PlanarNikodym.Analysis.Fourier.GlyzSpatialDilation
import PlanarNikodym.Analysis.Fourier.GlyzApproximationTransfer

/-! Unit-ball cone decoupling at an arbitrary physical frequency.
The physical Jacobian cancels exactly from both sides. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators Pointwise
namespace PlanarNikodym

theorem glyz_cone_frequency_scaled_local_lp (k A : ℕ) (hk : 0 < k)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B Q ε F rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q)
    (hε : 0 < ε) (hF : 0 < F) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (ρ : ℝ), 0 < ρ → ρ⁻¹ ≤ F * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace k) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzConeSpace k → ℂ)) ⊆
        (fun ξ => ρ • ξ) ''
          glyzConeBox k γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      (∫⁻ x in closedBall (0 : GlyzConeSpace k) 1, ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
          ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A x) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_cone_local_lp k A hk hp hβ hB hQ hε hF hrmin
  refine ⟨C, hC, fun γ hγ hder hdet N ρ hρ hρδ I f hI hf => ?_⟩
  let g : ℕ → SchwartzMap (GlyzConeSpace k) ℂ :=
    fun i => glyzSchwartzSpatialDilation ρ⁻¹ (inv_ne_zero hρ.ne') (f i)
  have hg (i : ℕ) (hi : i ∈ I) : Function.support (𝓕 (g i : GlyzConeSpace k → ℂ)) ⊆
      glyzConeBox k γ (glyzDyadicCenter N i) (glyzDyadicScale N) Q rmin rmax := by
    intro ξ hξ
    obtain ⟨η, hη, rfl⟩ := support_fourier_glyzSchwartzSpatialDilation _ _ (f i) hξ
    obtain ⟨v, hv, rfl⟩ := hf i hi hη
    simpa only [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul] using hv
  have h := hlocal γ hγ hder hdet N ρ⁻¹ (inv_pos.mpr hρ) hρδ I g hI hg
  let J := ENNReal.ofReal (((ρ⁻¹) ^ Module.finrank ℝ (GlyzConeSpace k))⁻¹)
  have hJ0 : J ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hJtop : J ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum (x : GlyzConeSpace k) : (∑ i ∈ I, g i) x = (∑ i ∈ I, f i) (ρ⁻¹ • x) := by
    simp only [sum_apply, g, glyzSchwartzSpatialDilation_apply]
  have hi (i : ℕ) :
      (∫⁻ x, ‖g i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A (ρ⁻¹ • x))) =
        J * ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A x) := by
    simp only [g, glyzSchwartzSpatialDilation_apply]
    simpa only [J, abs_of_pos (inv_pos.mpr (pow_pos (inv_pos.mpr hρ) _))] using
      glyz_lintegral_comp_smul
        (fun x => ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A x)) (inv_ne_zero hρ.ne')
  simp_rw [hsum, inv_inv, hi] at h
  rw [glyz_setLIntegral_comp_smul (fun x => ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ))
    (inv_pos.mpr hρ) ρ, inv_mul_cancel₀ hρ.ne', ← Finset.mul_sum] at h
  change J * _ ≤ _ * (J * _) at h
  have h' := mul_le_mul_right h J⁻¹
  simpa only [← mul_assoc, mul_left_comm J⁻¹ _ J, ENNReal.inv_mul_cancel hJ0 hJtop,
    one_mul, mul_one] using h'

end PlanarNikodym
