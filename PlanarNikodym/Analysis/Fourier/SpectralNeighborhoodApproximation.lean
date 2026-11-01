import PlanarNikodym.Analysis.Fourier.GlyzFourierProjector
import PlanarNikodym.Analysis.Fourier.UniformFourierMoments
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Actual Schwartz approximation with Fourier support in a prescribed
neighborhood. The error is controlled by the true Fourier mass outside
the smaller neighborhood; the cutoff is constructed by smooth separation. -/
noncomputable section
open Set Metric MeasureTheory FourierTransform
open scoped ContDiff FourierTransform Topology Manifold
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourierProjector_error_le_tail (f θ : SchwartzMap E ℂ)
    {S : Set E} (hS : MeasurableSet S)
    (hθ : ∀ ξ, ‖1 - θ ξ‖ ≤ 1) (hone : ∀ ξ ∈ S, θ ξ = 1) (x : E) :
    ‖f x - glyzFourierProjector θ f x‖ ≤
      ∫ ξ in Sᶜ, ‖𝓕 f ξ‖ := by
  let h := f - glyzFourierProjector θ f
  have he (ξ : E) : 𝓕 h ξ = 𝓕 f ξ * (1 - θ ξ) := by
    change 𝓕 (f - glyzFourierProjector θ f) ξ = _
    rw [show 𝓕 (f - glyzFourierProjector θ f) =
      𝓕 f - 𝓕 (glyzFourierProjector θ f) from
        map_sub (fourierCLM ℂ (SchwartzMap E ℂ)) _ _]
    change 𝓕 f ξ - 𝓕 (glyzFourierProjector θ f : E → ℂ) ξ = _
    rw [fourier_glyzFourierProjector]
    simp only [SchwartzMap.fourier_coe]
    ring
  have hm (ξ : E) : ‖𝓕 h ξ‖ ≤ Sᶜ.indicator (fun ζ => ‖𝓕 f ζ‖) ξ := by
    by_cases hξ : ξ ∈ S
    · rw [he, hone ξ hξ, sub_self, mul_zero, norm_zero]
      simp [hξ]
    · rw [indicator_of_mem (show ξ ∈ Sᶜ from hξ), he, norm_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hθ ξ) (norm_nonneg (𝓕 f ξ))
  calc
    _ = ‖h x‖ := rfl
    _ = ‖𝓕⁻ (𝓕 h) x‖ := by rw [fourierInv_fourier_eq]
    _ ≤ ∫ ξ, ‖𝓕 h ξ‖ := by
      rw [SchwartzMap.fourierInv_coe, glyz_fourierInv_eq_integral_char]
      apply (norm_integral_le_integral_norm _).trans_eq
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [norm_mul, Circle.norm_coe, one_mul]
    _ ≤ ∫ ξ, Sᶜ.indicator (fun ζ => ‖𝓕 f ζ‖) ξ :=
      integral_mono (𝓕 h).integrable.norm ((𝓕 f).integrable.norm.indicator hS.compl) hm
    _ = _ := integral_indicator hS.compl

omit [MeasurableSpace E] [BorelSpace E] in
/-- The cutoff takes real values in `[0,1]`, is one on the closed
`R`-neighborhood, and vanishes outside the closed `2R`-neighborhood. -/
theorem exists_schwartz_neighborhood_cutoff {K : Set E} (hK : IsCompact K)
    {R : ℝ} (hR : 0 < R) :
    ∃ θ : SchwartzMap E ℂ,
      (∀ ξ, ‖1 - θ ξ‖ ≤ 1) ∧
      (∀ ξ ∈ cthickening R K, θ ξ = 1) ∧
      Function.support θ ⊆ cthickening (2 * R) K := by
  obtain ⟨b, hb, hrange, hs, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, E))
      (n := (⊤ : ℕ∞)) (s := thickening (2 * R) K) (t := cthickening R K)
      isOpen_thickening isClosed_cthickening
      (cthickening_subset_thickening' (by positivity) (by linarith) K)
  have hbc : HasCompactSupport b := by
    apply HasCompactSupport.intro (hK.cthickening (r := 2 * R))
    intro ξ hξ
    apply Function.notMem_support.mp
    rw [hs]
    exact fun h => hξ (thickening_subset_cthickening _ _ h)
  have hbd : ContDiff ℝ ∞ b := contMDiff_iff_contDiff.mp hb
  let θ : SchwartzMap E ℂ :=
    (hbc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hbd)
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro ξ
    change ‖(1 : ℂ) - (b ξ : ℂ)‖ ≤ 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hrange (mem_range_self ξ)).2)]
    linarith [(hrange (mem_range_self ξ)).1]
  · intro ξ hξ
    change (b ξ : ℂ) = 1
    rw [(hone ξ).mp hξ, Complex.ofReal_one]
  · intro ξ hξ
    apply thickening_subset_cthickening _ _
    rw [← hs]
    exact fun hz => hξ (by change (b ξ : ℂ) = 0; rw [hz, Complex.ofReal_zero])

/-- Genuine support approximation of any Schwartz function, with the
true tail as its only error. No estimate for the original function is
assumed in constructing the approximant. -/
theorem exists_schwartz_neighborhood_approximation (f : SchwartzMap E ℂ)
    {K : Set E} (hK : IsCompact K) {R : ℝ} (hR : 0 < R) :
    ∃ F : SchwartzMap E ℂ,
      Function.support (𝓕 (F : E → ℂ)) ⊆ cthickening (2 * R) K ∧
      ∀ x, ‖f x - F x‖ ≤ ∫ ξ in (cthickening R K)ᶜ, ‖𝓕 f ξ‖ := by
  obtain ⟨θ, hb, hone, hs⟩ := exists_schwartz_neighborhood_cutoff hK hR
  exact ⟨glyzFourierProjector θ f,
    (support_fourier_glyzFourierProjector θ f).trans hs,
    fourierProjector_error_le_tail f θ isClosed_cthickening.measurableSet hb hone⟩

end PlanarNikodym
