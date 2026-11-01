import PlanarNikodym.Analysis.Fourier.GlyzCenteredParabolicExtension

/-! The actual polynomial extension satisfies the local decoupling
step, uniformly over all centers and parabolic scales. The moment
curve, its torsion, symbol estimates, Fourier concentration and L²
error conversion are all supplied by proved theorems. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_centered_parabolic_local_lp (d k W M : ℕ) (hk : 0 < k)
    (χ : GlyzConeSpace k → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d k → ℝ)
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    {K : Set Plane} (hK : IsCompact K)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {ε rmin rmax : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (u : GlyzLocalizedParabolicParameters d k), u.scale = 1 →
      ∀ (α : ℝ) (N : ℕ) (R T : ℝ), 0 < R → 0 < T →
      1 + 2 * ((1 + |α|) * T) ≤
        (rmin / 4) * (R / (2 * Real.pi)) * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → Plane → ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      (∀ i, MemLp (g i) 2 volume) → (∀ i, Function.support (g i) ⊆ K) →
      (∀ i ∈ I, Function.support (g i) ⊆ J i ×ˢ Icc rmin rmax) →
      let E := fun i x => χ x * polynomialExtension
        (glyzCompactParabolicAmplitude A H u.frozen u.δ u.δ_pos.ne' α)
        (g i) R (u.center + glyzMomentConeCoefficientEquiv k x)
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
  obtain ⟨β, B, hβ, hB, hj, hdet⟩ := exists_glyzEuclideanMomentCurve_bounds k
  obtain ⟨C, D, hC, hD, hb⟩ := glyz_parabolic_cone_local_lp_L2_error d k W M hk
    χ hχ hcχ A hA hcA H hH hcH
    (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap hK hp hβ hB hε hrmin
      (rmax := rmax)
  refine ⟨C, D, hC, hD, ?_⟩
  intro u hu α N R T hR hT hscale I J g hI hJ hJu hJc hg hgsK hgs
  let ga : ℕ → Plane → ℂ := fun i => glyzCenteredPolynomialInput u.center R (g i)
  have hga (i : ℕ) : MemLp (ga i) 2 volume :=
    memLp_glyzCenteredPolynomialInput u.center R (hg i)
  have hgaK (i : ℕ) : Function.support (ga i) ⊆ K :=
    (support_glyzCenteredPolynomialInput_subset u.center R (g i)).trans (hgsK i)
  have hgaJ (i : ℕ) (hi : i ∈ I) : Function.support (ga i) ⊆ J i ×ˢ Icc rmin rmax :=
    (support_glyzCenteredPolynomialInput_subset u.center R (g i)).trans (hgs i hi)
  have hn (i : ℕ) : lpNorm (ga i) 2 volume = lpNorm (g i) 2 volume :=
    lpNorm_glyzCenteredPolynomialInput u.center R (hg i).aestronglyMeasurable 2
  have he (i : ℕ) (x : GlyzConeSpace k) :
      oscillatoryConeExtension
        (glyzLocalizedParabolicAmplitude χ A
          (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap u)
        (glyzParabolicSample H (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap u)
        α (glyzCurveConeFrequency k (glyzEuclideanMomentCurve k) (R / (2 * Real.pi))) (ga i) x =
        χ x * polynomialExtension
          (glyzCompactParabolicAmplitude A H u.frozen u.δ u.δ_pos.ne' α)
          (g i) R (u.center + glyzMomentConeCoefficientEquiv k x) :=
    oscillatoryConeExtension_eq_centered_polynomialExtension χ A hA hcA H hH u hu α R
      (g i) (integrable_of_memLp_two_support_finite (hg i) hK.measure_ne_top (hgsK i)) x
  have hh := hb (glyzEuclideanMomentCurve k) (contDiff_glyzEuclideanMomentCurve k)
    hj hdet u α N (R / (2 * Real.pi)) T (div_pos hR (by positivity)) hT hscale
    I J ga hI hJ hJu hJc hga hgaK hgaJ
  simpa only [he, hn] using hh


theorem glyz_centered_parabolic_local_lp_L1_error (d k W M : ℕ) (hk : 0 < k)
    (χ : GlyzConeSpace k → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d k → ℝ)
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {ε rmin rmax : ℝ} (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ (u : GlyzLocalizedParabolicParameters d k), u.scale = 1 →
      ∀ (α : ℝ) (N : ℕ) (R T : ℝ), 0 < R → 0 < T →
      1 + 2 * ((1 + |α|) * T) ≤
        (rmin / 4) * (R / (2 * Real.pi)) * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → Plane → ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      (∀ i, Integrable (g i)) →
      (∀ i ∈ I, Function.support (g i) ⊆ J i ×ˢ Icc rmin rmax) →
      let E := fun i x => χ x * polynomialExtension
        (glyzCompactParabolicAmplitude A H u.frozen u.δ u.δ_pos.ne' α)
        (g i) R (u.center + glyzMomentConeCoefficientEquiv k x)
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
              volume (closedBall (0 : GlyzConeSpace k) 1)) := by
  obtain ⟨β, B, hβ, hB, hj, hdet⟩ := exists_glyzEuclideanMomentCurve_bounds k
  obtain ⟨C, D, hC, hD, hb⟩ := glyz_parabolic_cone_local_lp d k W M hk
    χ hχ hcχ A hA hcA H hH hcH
    (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap hp hβ hB hε hrmin
      (rmax := rmax)
  refine ⟨C, D, hC, hD, ?_⟩
  intro u hu α N R T hR hT hscale I J g hI hJ hJu hJc hg hgs
  let ga : ℕ → Plane → ℂ := fun i => glyzCenteredPolynomialInput u.center R (g i)
  have hga (i : ℕ) : Integrable (ga i) :=
    integrable_glyzCenteredPolynomialInput u.center R (hg i)
  have hgaJ (i : ℕ) (hi : i ∈ I) : Function.support (ga i) ⊆ J i ×ˢ Icc rmin rmax :=
    (support_glyzCenteredPolynomialInput_subset u.center R (g i)).trans (hgs i hi)
  have hn (i : ℕ) : (∫ y, ‖ga i y‖) = ∫ y, ‖g i y‖ := by
    simp only [ga, norm_glyzCenteredPolynomialInput]
  have he (i : ℕ) (x : GlyzConeSpace k) :
      oscillatoryConeExtension
        (glyzLocalizedParabolicAmplitude χ A
          (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap u)
        (glyzParabolicSample H (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap u)
        α (glyzCurveConeFrequency k (glyzEuclideanMomentCurve k) (R / (2 * Real.pi))) (ga i) x =
        χ x * polynomialExtension
          (glyzCompactParabolicAmplitude A H u.frozen u.δ u.δ_pos.ne' α)
          (g i) R (u.center + glyzMomentConeCoefficientEquiv k x) :=
    oscillatoryConeExtension_eq_centered_polynomialExtension χ A hA hcA H hH u hu α R
      (g i) (hg i) x
  have hh := hb (glyzEuclideanMomentCurve k) (contDiff_glyzEuclideanMomentCurve k)
    hj hdet u α N (R / (2 * Real.pi)) T (div_pos hR (by positivity)) hT hscale
    I J ga hI hJ hJu hJc hga hgaJ
  simpa only [he, hn] using hh

end PlanarNikodym
