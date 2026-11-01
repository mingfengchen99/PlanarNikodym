import PlanarNikodym.Analysis.Fourier.GlyzParabolicSymbol
import PlanarNikodym.Analysis.Fourier.OscillatoryConeSpectralApproximation

/-! Actual parabolic symbols localized at arbitrary output centers.
The inverse anisotropic dilation and every contracting local spatial
scale preserve uniform jets. A fixed cutoff provides a common compact
output support, including when the rescaled chart domains expand. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

theorem norm_iteratedFDeriv_affine_comp_le
    {E V F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] V) (b : V) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun z => f (b + L z)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (b + L x)‖ * ‖L‖ ^ j := by
  have he := L.iteratedFDeriv_comp_right
    (hf.comp ((contDiff_const (c := b)).add contDiff_id)) x
    (i := j) (by exact_mod_cast le_top)
  simp only [Function.comp_def, id_eq, iteratedFDeriv_comp_add_left] at he
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j f (b + L x)) (fun _ : Fin j => L)

structure GlyzLocalizedParabolicParameters (d n : ℕ) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  frozen : ℝ × Aux (d + 2)
  center : Aux (n + 1)
  scale : ℝ
  abs_scale_le_one : |scale| ≤ 1

section General
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def glyzCoefficientInsertion (d n : ℕ) (T : E →L[ℝ] Aux (n + 1)) :
    E →L[ℝ] CinematicAmplitudeVariables d n :=
  ((0 : E →L[ℝ] (ℝ × Aux (d + 2))).prod T).prod 0

@[simp] theorem glyzCoefficientInsertion_apply (d n : ℕ)
    (T : E →L[ℝ] Aux (n + 1)) (x : E) :
    glyzCoefficientInsertion d n T x = ((0, T x), 0) := rfl

def glyzParabolicSample {d n : ℕ} {F : Type}
    (B : GlyzParabolicSymbolVariables d n → F)
    (T : E →L[ℝ] Aux (n + 1)) (p : GlyzLocalizedParabolicParameters d n)
    (z : E × Plane) : F :=
  B (inverseCoefficientVariables (ℝ × Aux (d + 2)) n p.δ p.δ_pos.ne'
    ((p.frozen, p.center + p.scale • T z.1), z.2), p.δ)

theorem contDiff_glyzParabolicSample {d n : ℕ} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : GlyzParabolicSymbolVariables d n → F} (hB : ContDiff ℝ ∞ B)
    (T : E →L[ℝ] Aux (n + 1)) (p : GlyzLocalizedParabolicParameters d n) :
    ContDiff ℝ ∞ (glyzParabolicSample B T p) := by
  unfold glyzParabolicSample
  exact hB.comp (((inverseCoefficientVariables (ℝ × Aux (d + 2)) n p.δ
    p.δ_pos.ne').contDiff.comp
      (((contDiff_const (c := p.frozen)).prodMk ((contDiff_const (c := p.center)).add
        ((contDiff_const (c := p.scale)).smul (T.contDiff.comp contDiff_fst)))).prodMk
          contDiff_snd)).prodMk (contDiff_const (c := p.δ)))

theorem exists_uniform_glyzParabolicSample_fiber_jets {d n : ℕ} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : GlyzParabolicSymbolVariables d n → F)
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B)
    (T : E →L[ℝ] Aux (n + 1)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p y x,
      ‖iteratedFDeriv ℝ j (fun z => glyzParabolicSample B T p (z, y)) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_glyz_uniform_parabolic_symbol_jets B hB hcB j
  let L := glyzCoefficientInsertion d n T
  refine ⟨C * ‖L‖ ^ j, by positivity, fun p y x => ?_⟩
  let f : CinematicAmplitudeVariables d n → F := fun v =>
    B (inverseCoefficientVariables (ℝ × Aux (d + 2)) n p.δ p.δ_pos.ne' v, p.δ)
  have hf : ContDiff ℝ ∞ f := hB.comp
    ((inverseCoefficientVariables (ℝ × Aux (d + 2)) n p.δ p.δ_pos.ne').contDiff.prodMk
      contDiff_const)
  have he : (fun z => glyzParabolicSample B T p (z, y)) =
      (fun z => f (((p.frozen, p.center), y) + (p.scale • L) z)) := by
    funext z
    simp [glyzParabolicSample, f, L, glyzCoefficientInsertion, Prod.add_def,
      Prod.smul_def]
  rw [he]
  apply (norm_iteratedFDeriv_affine_comp_le hf (p.scale • L)
    ((p.frozen, p.center), y) j x).trans
  have hL : ‖p.scale • L‖ ≤ ‖L‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) p.abs_scale_le_one
  exact mul_le_mul
    (hb p.δ p.δ_pos p.δ_le_one _)
    (pow_le_pow_left₀ (norm_nonneg _) hL j)
    (by positivity) hC

def glyzLocalizedParabolicAmplitude {d n : ℕ}
    (χ : E → ℂ) (A : GlyzParabolicSymbolVariables d n → ℂ)
    (T : E →L[ℝ] Aux (n + 1)) (p : GlyzLocalizedParabolicParameters d n)
    (z : E × Plane) : ℂ :=
  χ z.1 * glyzParabolicSample A T p z

theorem contDiff_glyzLocalizedParabolicAmplitude {d n : ℕ}
    {χ : E → ℂ} (hχ : ContDiff ℝ ∞ χ)
    {A : GlyzParabolicSymbolVariables d n → ℂ} (hA : ContDiff ℝ ∞ A)
    (T : E →L[ℝ] Aux (n + 1)) (p : GlyzLocalizedParabolicParameters d n) :
    ContDiff ℝ ∞ (glyzLocalizedParabolicAmplitude χ A T p) :=
  (hχ.comp contDiff_fst).mul (contDiff_glyzParabolicSample hA T p)

theorem tsupport_glyzLocalizedParabolicAmplitude_fiber_subset {d n : ℕ}
    (χ : E → ℂ) (A : GlyzParabolicSymbolVariables d n → ℂ)
    (T : E →L[ℝ] Aux (n + 1))
    (p : GlyzLocalizedParabolicParameters d n) (y : Plane) :
    tsupport (fun x => glyzLocalizedParabolicAmplitude χ A T p (x, y)) ⊆ tsupport χ :=
  tsupport_mul_subset_left

theorem hasCompactSupport_glyzLocalizedParabolicAmplitude {d n : ℕ}
    {χ : E → ℂ} (hcχ : HasCompactSupport χ)
    {A : GlyzParabolicSymbolVariables d n → ℂ} (hcA : HasCompactSupport A)
    (T : E →L[ℝ] Aux (n + 1)) (p : GlyzLocalizedParabolicParameters d n) :
    HasCompactSupport (glyzLocalizedParabolicAmplitude χ A T p) := by
  let J := (fun v : GlyzParabolicSymbolVariables d n => v.1.2) '' tsupport A
  have hJ : IsCompact J := hcA.isCompact.image (continuous_snd.comp continuous_fst)
  apply HasCompactSupport.intro (hcχ.isCompact.prod hJ)
  intro z hz
  by_cases hx : z.1 ∈ tsupport χ
  · have hy : z.2 ∉ J := fun hy => hz ⟨hx, hy⟩
    have hAz : glyzParabolicSample A T p z = 0 := by
      unfold glyzParabolicSample
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hy ⟨(inverseCoefficientVariables (ℝ × Aux (d + 2)) n p.δ p.δ_pos.ne'
        ((p.frozen, p.center + p.scale • T z.1), z.2), p.δ), hmem, rfl⟩
    simp only [glyzLocalizedParabolicAmplitude, hAz, mul_zero]
  · simp only [glyzLocalizedParabolicAmplitude,
      image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem exists_uniform_glyzLocalizedParabolicAmplitude_fiber_jets {d n : ℕ}
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (A : GlyzParabolicSymbolVariables d n → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (T : E →L[ℝ] Aux (n + 1)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p y x,
      ‖iteratedFDeriv ℝ j
        (fun z => glyzLocalizedParabolicAmplitude χ A T p (z, y)) x‖ ≤ C := by
  choose D hD hd using exists_uniform_glyzParabolicSample_fiber_jets A hA hcA T
  let S : SchwartzMap E ℂ := hcχ.toSchwartzMap hχ
  let B : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i S
  have hB (i : ℕ) : 0 ≤ B i := apply_nonneg _ _
  let C := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * D (j - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hD (j - i))),
    fun p y x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le hχ
    ((contDiff_glyzParabolicSample hA T p).comp
      (contDiff_id.prodMk contDiff_const)) x (by exact_mod_cast le_top)).trans
  apply Finset.sum_le_sum
  intro i _
  have hχi : ‖iteratedFDeriv ℝ i χ x‖ ≤ B i := by
    have hS : (S : E → ℂ) = χ := rfl
    simpa only [B, hS] using S.norm_iteratedFDeriv_le_seminorm ℝ i x
  simpa only [mul_assoc, Function.comp_def, id_eq] using mul_le_mul_of_nonneg_left
    (mul_le_mul hχi (hd (j - i) p y x) (norm_nonneg _) (hB i))
    (Nat.cast_nonneg (j.choose i) : (0 : ℝ) ≤ j.choose i)

end General

section Fourier
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Actual localized inverse-chart symbols have uniform Fourier tails
for every output center, dilation scale and phase remainder size. -/
theorem exists_uniform_glyzLocalizedParabolic_fourier_tail {d n : ℕ}
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (A : GlyzParabolicSymbolVariables d n → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d n → ℝ)
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (T : E →L[ℝ] Aux (n + 1)) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α (ν : Plane → E) (hν : ContDiff ℝ ∞ ν)
      (g : Plane → ℂ) (hg : Integrable g) (S : Set E),
      (∀ y, g y ≠ 0 → ν y ∈ S) →
      ∀ U : ℝ, 0 < U →
      (∫ ξ in (Metric.cthickening ((1 + |α|) * U) S)ᶜ,
        ‖𝓕 (oscillatoryConeExtensionSchwartz
          (glyzLocalizedParabolicAmplitude χ A T p) (glyzParabolicSample H T p)
          (contDiff_glyzLocalizedParabolicAmplitude hχ hA T p)
          (contDiff_glyzParabolicSample hH T p)
          (hasCompactSupport_glyzLocalizedParabolicAmplitude hcχ hcA T p)
          α ν hν g hg) ξ‖) ≤
        (C * (1 + |α|) ^ (volume : Measure E).integrablePower * (U⁻¹) ^ M) *
          ∫ y, ‖g y‖ :=
  exists_uniform_oscillatoryConeExtension_fourier_tail
    (glyzLocalizedParabolicAmplitude χ A T) (glyzParabolicSample H T)
    (contDiff_glyzLocalizedParabolicAmplitude hχ hA T)
    (contDiff_glyzParabolicSample hH T)
    (hasCompactSupport_glyzLocalizedParabolicAmplitude hcχ hcA T)
    hcχ.isCompact (tsupport_glyzLocalizedParabolicAmplitude_fiber_subset χ A T)
    (exists_uniform_glyzLocalizedParabolicAmplitude_fiber_jets χ hχ hcχ A hA hcA T)
    (exists_uniform_glyzParabolicSample_fiber_jets H hH hcH T) M

/-- The compact symbol certificates are constructed from `A`, `H` and
the fixed cutoff. No quantitative symbol estimate is an assumption. -/
theorem exists_uniform_glyzLocalizedParabolic_spectral_approximation {d n : ℕ}
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (A : GlyzParabolicSymbolVariables d n → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d n → ℝ)
    (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (T : E →L[ℝ] Aux (n + 1)) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α (ν : Plane → E), ContDiff ℝ ∞ ν →
      ∀ (J : Set Plane), IsCompact J →
      ∀ (g : Plane → ℂ), Integrable g → Function.support g ⊆ J →
      ∀ U : ℝ, 0 < U → ∃ F : SchwartzMap E ℂ,
        Function.support (𝓕 (F : E → ℂ)) ⊆
          Metric.cthickening (2 * ((1 + |α|) * U)) (ν '' J) ∧
        ∀ x, ‖oscillatoryConeExtension
          (glyzLocalizedParabolicAmplitude χ A T p)
          (glyzParabolicSample H T p) α ν g x - F x‖ ≤
          (C * (1 + |α|) ^ (volume : Measure E).integrablePower * (U⁻¹) ^ M) *
            ∫ y, ‖g y‖ :=
  exists_uniform_oscillatoryConeExtension_spectral_approximation
    (glyzLocalizedParabolicAmplitude χ A T) (glyzParabolicSample H T)
    (contDiff_glyzLocalizedParabolicAmplitude hχ hA T)
    (contDiff_glyzParabolicSample hH T)
    (hasCompactSupport_glyzLocalizedParabolicAmplitude hcχ hcA T)
    hcχ.isCompact (tsupport_glyzLocalizedParabolicAmplitude_fiber_subset χ A T)
    (exists_uniform_glyzLocalizedParabolicAmplitude_fiber_jets χ hχ hcχ A hA hcA T)
    (exists_uniform_glyzParabolicSample_fiber_jets H hH hcH T) M

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem oscillatoryConeExtension_glyzLocalizedParabolicAmplitude {d n : ℕ}
    (χ : E → ℂ) (A : GlyzParabolicSymbolVariables d n → ℂ)
    (H : GlyzParabolicSymbolVariables d n → ℝ)
    (T : E →L[ℝ] Aux (n + 1)) (p : GlyzLocalizedParabolicParameters d n)
    (α : ℝ) (ν : Plane → E) (g : Plane → ℂ) (x : E) :
    oscillatoryConeExtension (glyzLocalizedParabolicAmplitude χ A T p)
      (glyzParabolicSample H T p) α ν g x =
      χ x * ∫ y, g y * (Real.fourierChar (inner ℝ x (ν y)) : ℂ) *
        glyzParabolicSample A T p (x, y) *
          Complex.exp (((α * glyzParabolicSample H T p (x, y) : ℝ) : ℂ) * Complex.I) := by
  unfold oscillatoryConeExtension
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [oscillatoryConeKernel, oscillatoryConeAmplitude,
    glyzLocalizedParabolicAmplitude, unitImaginaryExponential]
  ring

end Fourier

end PlanarNikodym
