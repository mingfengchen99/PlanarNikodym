import PlanarNikodym.Analysis.Fourier.CompactInputL2Error
import PlanarNikodym.Analysis.Fourier.GlyzOscillatoryConeDecoupling

/-! Local cone decoupling for the actual localized inverse-chart
parabolic symbols. Symbol estimates are derived from smooth compact
data, uniformly over all chart centers and anisotropic scales. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_parabolic_cone_local_lp (d k W M : ℕ) (hk : 0 < k)
    (χ : GlyzConeSpace k → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : GlyzParabolicSymbolVariables d k → ℂ)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (H : GlyzParabolicSymbolVariables d k → ℝ)
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (L : GlyzConeSpace k →L[ℝ] Aux (k + 1))
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ ∞ γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (u : GlyzLocalizedParabolicParameters d k) (α : ℝ)
        (N : ℕ) (ρ T : ℝ), 0 < ρ → 0 < T →
      1 + 2 * ((1 + |α|) * T) ≤ (rmin / 4) * ρ * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → Plane → ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      (∀ i, Integrable (g i)) → (∀ i ∈ I, Function.support (g i) ⊆ J i ×ˢ Icc rmin rmax) →
      let E := fun i => oscillatoryConeExtension
        (glyzLocalizedParabolicAmplitude χ a L u) (glyzParabolicSample H L u)
        α (glyzCurveConeFrequency k γ ρ) (g i)
      let e := fun i => (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower *
        (T⁻¹) ^ M) * ∫ y, ‖g i y‖
      let weight := fun x : GlyzConeSpace k => ENNReal.ofReal (glyzNormWeight W x)
      (∫⁻ x in closedBall (0 : GlyzConeSpace k) 1, ‖∑ i ∈ I, E i x‖ₑ ^ (p : ℝ)) ≤
        (2 : ℝ≥0∞) ^ (p : ℝ) *
          (ENNReal.ofReal (C * (2 : ℝ) ^
            (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
              ((2 : ℝ≥0∞) ^ (p : ℝ) *
                ((∑ i ∈ I, ∫⁻ x, ‖E i x‖ₑ ^ (p : ℝ) * weight x) +
                  (∑ i ∈ I, ENNReal.ofReal (e i) ^ (p : ℝ)) * ∫⁻ x, weight x)) +
            ENNReal.ofReal (∑ i ∈ I, e i) ^ (p : ℝ) *
              volume (closedBall (0 : GlyzConeSpace k) 1)) :=
  glyz_oscillatory_cone_local_lp k W M hk
    (glyzLocalizedParabolicAmplitude χ a L) (glyzParabolicSample H L)
    (contDiff_glyzLocalizedParabolicAmplitude hχ ha L)
    (contDiff_glyzParabolicSample hH L)
    (hasCompactSupport_glyzLocalizedParabolicAmplitude hcχ hca L)
    hcχ.isCompact (tsupport_glyzLocalizedParabolicAmplitude_fiber_subset χ a L)
    (exists_uniform_glyzLocalizedParabolicAmplitude_fiber_jets χ hχ hcχ a ha hca L)
    (exists_uniform_glyzParabolicSample_fiber_jets H hH hcH L)
    hp hβ hB hε hrmin

/-- Fixed compact frequency support converts the actual error to the
input L² norm. All constants precede the local chart and scale data. -/
theorem glyz_parabolic_cone_local_lp_L2_error (d k W M : ℕ) (hk : 0 < k)
    (χ : GlyzConeSpace k → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : GlyzParabolicSymbolVariables d k → ℂ)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (H : GlyzParabolicSymbolVariables d k → ℝ)
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (L : GlyzConeSpace k →L[ℝ] Aux (k + 1))
    {K : Set Plane} (hK : IsCompact K)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ ∞ γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (u : GlyzLocalizedParabolicParameters d k) (α : ℝ)
        (N : ℕ) (ρ T : ℝ), 0 < ρ → 0 < T →
      1 + 2 * ((1 + |α|) * T) ≤ (rmin / 4) * ρ * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → Plane → ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      (∀ i, MemLp (g i) 2 volume) → (∀ i, Function.support (g i) ⊆ K) →
      (∀ i ∈ I, Function.support (g i) ⊆ J i ×ˢ Icc rmin rmax) →
      let E := fun i => oscillatoryConeExtension
        (glyzLocalizedParabolicAmplitude χ a L u) (glyzParabolicSample H L u)
        α (glyzCurveConeFrequency k γ ρ) (g i)
      let e := fun i => (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower *
        (T⁻¹) ^ M) * lpNorm (g i) 2 volume
      let weight := fun x : GlyzConeSpace k => ENNReal.ofReal (glyzNormWeight W x)
      (∫⁻ x in closedBall (0 : GlyzConeSpace k) 1, ‖∑ i ∈ I, E i x‖ₑ ^ (p : ℝ)) ≤
        (2 : ℝ≥0∞) ^ (p : ℝ) *
          (ENNReal.ofReal (C * (2 : ℝ) ^
            (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
              ((2 : ℝ≥0∞) ^ (p : ℝ) *
                ((∑ i ∈ I, ∫⁻ x, ‖E i x‖ₑ ^ (p : ℝ) * weight x) +
                  (∑ i ∈ I, ENNReal.ofReal (e i) ^ (p : ℝ)) * ∫⁻ x, weight x)) +
            ENNReal.ofReal (∑ i ∈ I, e i) ^ (p : ℝ) *
              volume (closedBall (0 : GlyzConeSpace k) 1)) := by
  obtain ⟨C, D, hC, hD, hb⟩ := glyz_parabolic_cone_local_lp d k W M hk
    χ hχ hcχ a ha hca H hH hcH L hp hβ hB hε hrmin (rmax := rmax)
  refine ⟨C, D * Real.sqrt (volume K).toReal, hC, by positivity, ?_⟩
  intro γ hγ hj hdet u α N ρ T hρ hT hscale I J g hI hJ hJu hJc hg hgsK hgs
  have hi (i : ℕ) : Integrable (g i) :=
    integrable_of_memLp_two_support_finite (hg i) hK.measure_ne_top (hgsK i)
  have herr (i : ℕ) :
      (D * (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower * (T⁻¹) ^ M) *
        (∫ y, ‖g i y‖) ≤
      (D * Real.sqrt (volume K).toReal *
        (1 + |α|) ^ (volume : Measure (GlyzConeSpace k)).integrablePower * (T⁻¹) ^ M) *
          lpNorm (g i) 2 volume := by
    apply (mul_le_mul_of_nonneg_left
      (integral_norm_le_sqrt_measure_mul_lpNorm_two (hg i) hK.measure_ne_top (hgsK i))
      (by positivity)).trans_eq
    ring
  have hh := hb γ hγ hj hdet u α N ρ T hρ hT hscale I J g hI hJ hJu hJc hi hgs
  apply hh.trans
  dsimp only
  apply mul_le_mul_right
  apply add_le_add
  · apply mul_le_mul_right
    apply mul_le_mul_right
    apply add_le_add (le_refl _)
    apply mul_le_mul_left
    exact Finset.sum_le_sum (fun i _ =>
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (herr i)) (by positivity))
  · apply mul_le_mul_left
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (Finset.sum_le_sum (fun i _ => herr i))) (by positivity)

end PlanarNikodym
