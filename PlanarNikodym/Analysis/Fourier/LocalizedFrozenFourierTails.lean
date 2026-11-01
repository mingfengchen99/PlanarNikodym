import PlanarNikodym.Analysis.Fourier.LocalizedVariableExtension

/-! All Fourier tails of the true localized frozen amplitude, uniformly
over compact spatial centers, every input frequency, and the normalized
Taylor parameters in `[0,1]`. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem localizedFrozenAmplitudeSchwartz_eq_zero_of_not_mem_input_support
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (w : E) {y : Plane} (hy : y ∉ Prod.snd '' tsupport a) (α δ : ℝ) :
    localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ ((w, y), α, δ) = 0 := by
  ext z
  have hz : a (w + δ • z, y) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hy ⟨(w + δ • z, y), h, rfl⟩
  simp [localizedFrozenAmplitudeSchwartz_apply, localizedFrozenAmplitude,
    frozenSpatialAmplitude, hz]

theorem exists_uniform_localizedFrozenAmplitude_fourier_moment
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set E} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ y : Plane, ∀ α δ : ℝ,
      α ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 →
      (∫ ξ : E, ‖ξ‖ ^ k *
        ‖𝓕 (localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ ((w, y), α, δ)) ξ‖) ≤ C := by
  let P := {q : (E × Plane) × ℝ × ℝ //
    q.1.1 ∈ K ∧ q.2.1 ∈ Icc (0 : ℝ) 1 ∧ q.2.2 ∈ Icc (0 : ℝ) 1}
  let S : P → SchwartzMap E ℂ := fun q =>
    localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ q.1
  have hs : ∀ q : P, tsupport (S q) ⊆ tsupport χ := fun q =>
    tsupport_localizedFrozenAmplitude_fiber_subset χ a Φ q.1
  have hjet : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ q : P, ∀ z,
      ‖iteratedFDeriv ℝ j (S q) z‖ ≤ B := by
    intro j
    obtain ⟨B, hB, hb⟩ := localizedFrozenAmplitude_uniform_jets
      χ hχ hcχ a ha Φ hΦ (hK.prod (hca.isCompact.image continuous_snd)) j
    refine ⟨B, hB, fun q z => ?_⟩
    by_cases hy : q.1.1.2 ∈ Prod.snd '' tsupport a
    · exact hb q.1 ⟨q.2.1, hy⟩ q.2.2.1 q.2.2.2 z
    · have hz : S q = 0 :=
        localizedFrozenAmplitudeSchwartz_eq_zero_of_not_mem_input_support
          χ hχ hcχ a ha Φ hΦ q.1.1.1 hy q.1.2.1 q.1.2.2
      simpa only [hz, FunLike.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, norm_zero] using hB
  obtain ⟨C, hC, hb⟩ := exists_uniform_compact_schwartz_image_moment_bound volume
    ((FourierTransform.fourierCLM ℂ (SchwartzMap E ℂ)).restrictScalars ℝ)
    S hcχ.isCompact hs hjet k
  exact ⟨C, hC, fun w hw y α δ hα hδ => hb ⟨((w, y), α, δ), hw, hα, hδ⟩⟩

theorem exists_uniform_localizedFrozenAmplitude_fourier_tail
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set E} (hK : IsCompact K) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ K, ∀ y : Plane, ∀ α δ R : ℝ,
      α ∈ Icc (0 : ℝ) 1 → δ ∈ Icc (0 : ℝ) 1 → 0 < R →
      (∫ ξ in {ξ : E | R ≤ ‖ξ‖},
        ‖𝓕 (localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ ((w, y), α, δ)) ξ‖) ≤
          C * (R⁻¹) ^ M := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_localizedFrozenAmplitude_fourier_moment
    χ hχ hcχ a ha hca Φ hΦ hK M
  refine ⟨C, hC, fun w hw y α δ R hα hδ hR => ?_⟩
  have ht := schwartz_integral_moment_tail_le volume
    (𝓕 (localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ ((w, y), α, δ))) 0 M hR
  simp only [pow_zero, one_mul, zero_add] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_left (hb w hw y α δ hα hδ)
    (by positivity)).trans_eq (mul_comm _ _))

end PlanarNikodym
