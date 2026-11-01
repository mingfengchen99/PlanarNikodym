import PlanarNikodym.Analysis.Fourier.GlyzSmoothColorAssembly
import PlanarNikodym.Analysis.Fourier.GlyzShiftedSmoothPartition

/-! Exact finite reindexing of smooth pieces into grid slots. Empty
slots contribute zero; occupied slots retain their original functions. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

/-- Zero extension along an injection preserves every finite sum whose
summand vanishes at zero. This includes the actual extension energy. -/
theorem glyz_sum_comp_extend {ι κ V A : Type*} [Fintype ι] [Fintype κ]
    [Zero V] [AddCommMonoid A] (f : ι → κ) (hf : Function.Injective f)
    (g : ι → V) (H : V → A) (hH : H 0 = 0) :
    (∑ b, H (Function.extend f g (fun _ => 0) b)) = ∑ i, H (g i) := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image f, H (Function.extend f g (fun _ => 0) b) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      have hn : ¬ ∃ i, f i = b := by simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hb
      rw [Function.extend_apply' _ _ _ hn, hH]
    _ = ∑ i, H (Function.extend f g (fun _ => 0) (f i)) := by
      rw [Finset.sum_image]
      exact fun i _ j _ he => hf he
    _ = _ := by simp only [hf.extend_apply]

/-- An injected family retains its original support at occupied slots
and has empty support elsewhere. -/
theorem glyz_extend_cutoff_support {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) (χ : ι → ℝ → ℝ) (U : κ → Set ℝ)
    (hs : ∀ i, tsupport (χ i) ⊆ U (f i)) (b : κ) :
    tsupport (Function.extend f χ (fun _ => 0) b) ⊆ U b := by
  classical
  by_cases hb : ∃ i, f i = b
  · obtain ⟨i, rfl⟩ := hb
    simpa only [hf.extend_apply] using hs i
  · rw [Function.extend_apply' _ _ _ hb]
    simp

theorem continuous_glyz_extend_cutoff {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) (χ : ι → ℝ → ℝ)
    (hχ : ∀ i, Continuous (χ i)) (b : κ) :
    Continuous (Function.extend f χ (fun _ => 0) b) := by
  classical
  by_cases hb : ∃ i, f i = b
  · obtain ⟨i, rfl⟩ := hb
    simpa only [hf.extend_apply] using hχ i
  · rw [Function.extend_apply' _ _ _ hb]
    exact continuous_const

theorem glyz_extend_cutoff_nonneg {ι κ : Type*} (f : ι → κ)
    (hf : Function.Injective f) (χ : ι → ℝ → ℝ)
    (hχ : ∀ i t, 0 ≤ χ i t) (b : κ) (t : ℝ) :
    0 ≤ Function.extend f χ (fun _ => 0) b t := by
  classical
  by_cases hb : ∃ i, f i = b
  · obtain ⟨i, rfl⟩ := hb
    simpa only [hf.extend_apply] using hχ i t
  · rw [Function.extend_apply' _ _ _ hb]
    exact le_rfl

/-- No averaging or norm comparison occurs when a smooth family is
placed in distinct grid slots: the sum of actual operator powers is
unchanged. -/
theorem glyzRawExtension_power_sum_extend {P ι κ : Type}
    [Fintype ι] [Fintype κ] [MeasurableSpace P]
    (μ : Measure P) (Φ : P × ℝ → ℝ) (a : P × Plane → ℂ)
    (g : Plane → ℂ) (r : ℝ) {p : ℝ} (hp : 0 < p)
    (f : ι → κ) (hf : Function.Injective f) (χ : ι → ℝ → ℝ) :
    (∑ b, ∫⁻ x, ‖glyzRawExtension Φ a
      (glyzColorInput (Function.extend f χ (fun _ => 0) b) g) r x‖ₑ ^ p ∂μ) =
      ∑ i, ∫⁻ x, ‖glyzRawExtension Φ a (glyzColorInput (χ i) g) r x‖ₑ ^ p ∂μ := by
  apply glyz_sum_comp_extend f hf χ (fun θ =>
    ∫⁻ x, ‖glyzRawExtension Φ a (glyzColorInput θ g) r x‖ₑ ^ p ∂μ)
  simp [glyzColorInput, glyzRawExtension, hp]

end PlanarNikodym
