import PlanarNikodym.Analysis.Fourier.GlyzScaledConeLocalization
import PlanarNikodym.Analysis.Fourier.SpectralNeighborhoodApproximation

/-! Local decoupling with the actual Fourier tail as error. This theorem
constructs all supported approximants; no decoupling or support premise
is imposed on the original Schwartz functions. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators Pointwise
namespace PlanarNikodym

def glyzConeSpectralTail (k : ℕ) (γ : ℝ → GlyzSpace k) (J : Set ℝ)
    (rmin rmax ρ R : ℝ) (f : SchwartzMap (GlyzConeSpace k) ℂ) : ℝ :=
  ∫ ξ in (cthickening R ((fun v : GlyzConeSpace k => ρ • v) ''
    glyzConeArc k γ J rmin rmax))ᶜ, ‖𝓕 f ξ‖

/-- All constants precede the curve, depth, physical frequency, spectral
cutoff and actual functions. `1+2R` simultaneously pays for physical
localization and the actual spectral neighborhood. -/
theorem glyz_cone_spectral_local_lp (k A : ℕ) (hk : 0 < k)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B ε rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B)
    (hε : 0 < ε) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (ρ R : ℝ), 0 < ρ → 0 < R →
      1 + 2 * R ≤ (rmin / 4) * ρ * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (J : ℕ → Set ℝ) (g : ℕ → SchwartzMap (GlyzConeSpace k) ℂ),
      I ⊆ Finset.range (2 ^ N) → (∀ i, IsCompact (J i)) →
      (∀ i ∈ I, J i ⊆ Icc (0 : ℝ) 1) →
      (∀ i ∈ I, ∀ t ∈ J i, |t - glyzDyadicCenter N i| ≤ glyzDyadicScale N) →
      let e := fun i => glyzConeSpectralTail k γ (J i) rmin rmax ρ R (g i)
      let W := fun x : GlyzConeSpace k => ENNReal.ofReal (glyzNormWeight A x)
      (∫⁻ x in closedBall (0 : GlyzConeSpace k) 1, ‖(∑ i ∈ I, g i) x‖ₑ ^ (p : ℝ)) ≤
        (2 : ℝ≥0∞) ^ (p : ℝ) *
          (ENNReal.ofReal (C * (2 : ℝ) ^
            (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
              ((2 : ℝ≥0∞) ^ (p : ℝ) *
                ((∑ i ∈ I, ∫⁻ x, ‖g i x‖ₑ ^ (p : ℝ) * W x) +
                  (∑ i ∈ I, ENNReal.ofReal (e i) ^ (p : ℝ)) * ∫⁻ x, W x)) +
            ENNReal.ofReal (∑ i ∈ I, e i) ^ (p : ℝ) *
              volume (closedBall (0 : GlyzConeSpace k) 1)) := by
  let S := rmin / 4
  have hS : 0 < S := by dsimp [S]; positivity
  obtain ⟨Q, hQ, harc⟩ := exists_uniform_glyz_cone_arc_neighborhood_support k hβ hB hS hrmin
  obtain ⟨C, hC, hlocal⟩ := glyz_cone_frequency_scaled_local_lp k A hk hp
    hβ hB hQ hε hS (half_pos hrmin) (rmax := rmax + rmin / 2)
  refine ⟨C, hC, fun γ hγ hder hdet N ρ R hρ hR hscale I J g hI hJ hJunit hJcenter => ?_⟩
  let K : ℕ → Set (GlyzConeSpace k) := fun i =>
    (fun ξ : GlyzConeSpace k => ρ • ξ) '' glyzConeArc k γ (J i) rmin rmax
  have hK (i : ℕ) : IsCompact (K i) :=
    (isCompact_glyzConeArc k γ hγ.continuous (J i) (hJ i) rmin rmax).image (by fun_prop)
  have hex (i : ℕ) := exists_schwartz_neighborhood_approximation (g i) (hK i) hR
  choose f hf he using hex
  have hδ : 0 < glyzDyadicScale N := glyzDyadicScale_pos N
  have hδ1 : glyzDyadicScale N ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hsmall : S * glyzDyadicScale N ^ k ≤ rmin / 2 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := k) hδ.le hδ1) hS.le
    dsimp [S] at h ⊢
    nlinarith
  have hthick : 2 * R / ρ ≤ S * glyzDyadicScale N ^ k := by
    rw [div_le_iff₀ hρ]
    dsimp [S]
    nlinarith
  have hfreq : ρ⁻¹ ≤ S * glyzDyadicScale N ^ k := by
    rw [← one_div, div_le_iff₀ hρ]
    dsimp [S]
    nlinarith
  have hfs (i : ℕ) (hi : i ∈ I) : Function.support (𝓕 (f i : GlyzConeSpace k → ℂ)) ⊆
      (fun ξ => ρ • ξ) '' glyzConeBox k γ (glyzDyadicCenter N i) (glyzDyadicScale N)
        Q (rmin / 2) (rmax + rmin / 2) := by
    intro ξ hξ
    have hξ' := hf i hξ
    have hnorm : ρ⁻¹ • ξ ∈ glyzConeArc k γ (J i) rmin rmax +
        closedBall (0 : GlyzConeSpace k) (2 * R / ρ) :=
      glyz_inverse_dilation_neighborhood
        (isCompact_glyzConeArc k γ hγ.continuous (J i) (hJ i) rmin rmax)
        hρ (by positivity) ⟨ξ, hξ', rfl⟩
    have hbox := harc γ hγ hder hdet (glyzDyadicCenter N i)
      (glyzDyadicCenter_mem_Icc (Finset.mem_range.mp (hI hi)))
      (glyzDyadicScale N) rmax hδ hδ1 hsmall (J i) (hJunit i hi) (hJcenter i hi)
      ((add_subset_add (Subset.refl _) (closedBall_subset_closedBall hthick)) hnorm)
    exact ⟨ρ⁻¹ • ξ, hbox, by simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]⟩
  have hd := hlocal γ hγ hder hdet N ρ hρ hfreq I f hI hfs
  have ht := glyz_finite_approximation_transfer volume I
    (fun i x => g i x) (fun i x => f i x)
    (fun i => glyzConeSpectralTail k γ (J i) rmin rmax ρ R (g i))
    (fun x => ENNReal.ofReal (glyzNormWeight A x))
    (ENNReal.measurable_ofReal.comp (continuous_glyzNormWeight A).measurable)
    (closedBall (0 : GlyzConeSpace k) 1) p.coe_nonneg _
    (fun i _ => he i) (by simpa only [sum_apply] using hd)
  simpa only [sum_apply] using ht

end PlanarNikodym
