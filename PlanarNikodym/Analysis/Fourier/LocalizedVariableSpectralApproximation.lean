import PlanarNikodym.Analysis.Fourier.FrozenFrequencyRepresentation
import PlanarNikodym.Analysis.Fourier.FourierSuperpositionTail

/-! Actual spectral approximation of a variable-coefficient extension
on a small spatial ball. Compact smooth data construct the uniform
arbitrary-order error, and the approximant has genuine Fourier support
near the frozen gradient cone. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_uniform_localizedVariableExtension_fourier_tail
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set E} (hK : IsCompact K) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ L δ : ℝ,
      L * δ ^ 2 ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 →
      ∀ (g : Plane → ℂ) (hg : Integrable g) (S : Set E),
      (∀ y, g y ≠ 0 → frozenSpatialFrequency Φ w (L * δ) y ∈ S) →
      ∀ R : ℝ, 0 < R →
      (∫ ξ in (cthickening R S)ᶜ,
        ‖𝓕 (localizedVariableExtensionSchwartz χ hχ hcχ a ha hca Φ hΦ L w δ g hg) ξ‖) ≤
          (C * (R⁻¹) ^ M) * ∫ y, ‖g y‖ := by
  obtain ⟨D, _, hD⟩ := exists_uniform_localizedFrozenAmplitude_fourier_moment
    χ hχ hcχ a ha hca Φ hΦ hK 0
  obtain ⟨C, hC, ht⟩ := exists_uniform_localizedFrozenAmplitude_fourier_tail
    χ hχ hcχ a ha hca Φ hΦ hK M
  refine ⟨C, hC, fun w hw L δ hα hδ g hg S hS R hR => ?_⟩
  let B : E × Plane → ℂ := fun q =>
    𝓕 (localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ
      ((w, q.2), L * δ ^ 2, δ)) q.1
  have hB : Continuous B := by
    change Continuous (fun q : E × Plane =>
      𝓕 (fun z => localizedFrozenKernel χ a Φ w (L * δ ^ 2) δ (z, q.2)) q.1)
    exact continuous_compactKernel_partialFourier
      (contDiff_localizedFrozenKernel hχ ha hΦ w (L * δ ^ 2) δ)
      (hasCompactSupport_localizedFrozenKernel hcχ hca Φ w (L * δ ^ 2) δ)
  have hi (y : Plane) : Integrable (fun ξ => B (ξ, y)) :=
    (𝓕 (localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ ((w, y), L * δ ^ 2, δ))).integrable
  have hD' (y : Plane) : (∫ ξ, ‖B (ξ, y)‖) ≤ D := by
    simpa only [B, pow_zero, one_mul] using hD w hw y (L * δ ^ 2) δ hα hδ
  have ht' (y : Plane) :
      (∫ ξ in {ξ : E | R ≤ ‖ξ‖}, ‖B (ξ, y)‖) ≤ C * (R⁻¹) ^ M :=
    ht w hw y (L * δ ^ 2) δ R hα hδ hR
  have hvS (y : Plane) (hy : frozenSpatialData Φ L w g y ≠ 0) :
      frozenSpatialFrequency Φ w (L * δ) y ∈ S := by
    apply hS y
    intro hz
    exact hy (by simp [frozenSpatialData, hz])
  have hh := integral_fourier_superposition_tail_le volume
    (integrable_frozenSpatialData hΦ L w hg) hB
    (continuous_frozenSpatialFrequency hΦ w (L * δ)) hi hD' hvS ht'
  simp_rw [norm_frozenSpatialData] at hh
  simpa only [fourier_localizedVariableExtensionSchwartz, B] using hh

/-- The constant is chosen before the spatial center, physical scale,
input frequency patch, input function and spectral cutoff radius.
Only the actual smooth amplitude and phase determine it. -/
theorem exists_uniform_localizedVariableExtension_spectral_approximation
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set E} (hK : IsCompact K) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ L δ : ℝ,
      L * δ ^ 2 ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 →
      ∀ (J : Set Plane), IsCompact J →
      ∀ (g : Plane → ℂ), Integrable g → Function.support g ⊆ J →
      ∀ R : ℝ, 0 < R → ∃ F : SchwartzMap E ℂ,
        Function.support (𝓕 (F : E → ℂ)) ⊆
          cthickening (2 * R) (frozenSpatialFrequency Φ w (L * δ) '' J) ∧
        ∀ z, ‖localizedVariableExtension χ a Φ L w δ g z - F z‖ ≤
          (C * (R⁻¹) ^ M) * ∫ y, ‖g y‖ := by
  obtain ⟨C, hC, ht⟩ := exists_uniform_localizedVariableExtension_fourier_tail
    χ hχ hcχ a ha hca Φ hΦ hK M
  refine ⟨C, hC, fun w hw L δ hα hδ J hJ g hg hgs R hR => ?_⟩
  let G := localizedVariableExtensionSchwartz χ hχ hcχ a ha hca Φ hΦ L w δ g hg
  obtain ⟨F, hs, he⟩ := exists_schwartz_neighborhood_approximation G
    (hJ.image (continuous_frozenSpatialFrequency hΦ w (L * δ))) hR
  refine ⟨F, hs, fun z => (he z).trans ?_⟩
  exact ht w hw L δ hα hδ g hg (frozenSpatialFrequency Φ w (L * δ) '' J)
    (fun y hy => ⟨y, hgs hy, rfl⟩) R hR

/-- Physical radius `ρ ≤ √L` gives the normalized Taylor parameters
used above. The support center is precisely `ρ η ∇Φ/(2π)`. -/
theorem exists_uniform_physical_localizedVariableExtension_approximation
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set E} (hK : IsCompact K) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ L ρ : ℝ,
      1 ≤ ρ → ρ ^ 2 ≤ L →
      ∀ (J : Set Plane), IsCompact J →
      ∀ (g : Plane → ℂ), Integrable g → Function.support g ⊆ J →
      ∀ R : ℝ, 0 < R → ∃ F : SchwartzMap E ℂ,
        Function.support (𝓕 (F : E → ℂ)) ⊆
          cthickening (2 * R) (frozenSpatialFrequency Φ w ρ '' J) ∧
        ∀ z, ‖localizedVariableExtension χ a Φ L w (ρ / L) g z - F z‖ ≤
          (C * (R⁻¹) ^ M) * ∫ y, ‖g y‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_localizedVariableExtension_spectral_approximation
    χ hχ hcχ a ha hca Φ hΦ hK M
  refine ⟨C, hC, fun w hw L ρ hρ hscale J hJ g hg hgs R hR => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hL : 0 < L := lt_of_lt_of_le (sq_pos_of_pos hρ0) hscale
  have hρL : ρ ≤ L := by nlinarith
  have hδ : ρ / L ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hρ0.le hL.le, (div_le_one hL).mpr hρL⟩
  have heα : L * (ρ / L) ^ 2 = ρ ^ 2 / L := by field_simp
  have hα : L * (ρ / L) ^ 2 ∈ Icc (0 : ℝ) 1 := by
    rw [heα]
    exact ⟨div_nonneg (sq_nonneg _) hL.le, (div_le_one hL).mpr hscale⟩
  have heρ : L * (ρ / L) = ρ := by field_simp
  simpa only [heρ] using hb w hw L (ρ / L) hα hδ J hJ g hg hgs R hR

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A uniform pointwise approximation controls every local weighted
`Lᵖ` error through the mass of the weight measure. -/
theorem localizedVariableExtension_approximation_eLpNorm
    (χ : E → ℂ) (a : E × Plane → ℂ) (Φ : E × ℝ → ℝ)
    (L : ℝ) (w : E) (δ : ℝ) (g : Plane → ℂ) (F : SchwartzMap E ℂ)
    {B : ℝ} (hB : ∀ z, ‖localizedVariableExtension χ a Φ L w δ g z - F z‖ ≤ B)
    (μ : Measure E) (p : ℝ≥0∞) :
    eLpNorm (fun z => localizedVariableExtension χ a Φ L w δ g z - F z) p μ ≤
      μ univ ^ p.toReal⁻¹ * ENNReal.ofReal B :=
  eLpNorm_le_of_ae_bound (ae_of_all _ hB)

end PlanarNikodym
