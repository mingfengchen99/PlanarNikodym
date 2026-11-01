import PlanarNikodym.Analysis.Fourier.GlyzFourierSlice
import PlanarNikodym.Analysis.Fourier.GlyzMixedNorm
import PlanarNikodym.Analysis.Fourier.GlyzTaylorDecoupling

/-! Cylindrical decoupling for actual Schwartz functions.
Fourier support of each spatial slice follows from the proved marginal
formula. Tonelli and finite Minkowski lift the lower-dimensional estimate
without a loss depending on the number of slices or Fourier pieces. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem glyz_lintegral_withLp_eq_slices
    (F : WithLp 2 (H × V) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z) = ∫⁻ y : V, ∫⁻ x : H, F (WithLp.toLp 2 (x, y)) := by
  rw [← (WithLp.volume_preserving_toLp H V).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (H × V)).measurableEmbedding F]
  exact lintegral_prod_symm _ (hF.comp
    (MeasurableEquiv.toLp 2 (H × V)).measurable).aemeasurable

theorem glyz_cylindrical_power_decoupling
    (I : Finset ℕ) (Ω : ℕ → Set H) (hΩ : ∀ i ∈ I, IsClosed (Ω i))
    (f : ℕ → SchwartzMap (WithLp 2 (H × V)) ℂ)
    (hf : ∀ i ∈ I,
      Function.support (𝓕 (f i : WithLp 2 (H × V) → ℂ)) ⊆
        {z | (WithLp.ofLp z).1 ∈ Ω i})
    {p : ℝ} (hp : 2 ≤ p) (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (hdec : ∀ g : ℕ → SchwartzMap H ℂ,
      (∀ i ∈ I, Function.support (𝓕 (g i : H → ℂ)) ⊆ Ω i) →
      (∫⁻ x, ‖(∑ i ∈ I, g i) x‖ₑ ^ p) ≤
        D * (∑ i ∈ I, (∫⁻ x, ‖g i x‖ₑ ^ p) ^ (2 / p)) ^ (p / 2)) :
    (∫⁻ z, ‖(∑ i ∈ I, f i) z‖ₑ ^ p) ≤
      D * (∑ i ∈ I, (∫⁻ z, ‖f i z‖ₑ ^ p) ^ (2 / p)) ^ (p / 2) := by
  let U : ℕ → V → ℝ≥0∞ := fun i y =>
    ∫⁻ x : H, ‖f i (WithLp.toLp 2 (x, y))‖ₑ ^ p
  have hU (i : ℕ) : Measurable (U i) := by
    exact Measurable.lintegral_prod_left'
      (f := fun z : H × V => ‖f i (WithLp.toLp 2 z)‖ₑ ^ p)
      ((ENNReal.continuous_rpow_const.comp
        (((f i).continuous.comp
          (WithLp.prodContinuousLinearEquiv 2 ℝ H V).symm.continuous).enorm)).measurable)
  have hslice (y : V) :
      (∫⁻ x : H, ‖(∑ i ∈ I, f i) (WithLp.toLp 2 (x, y))‖ₑ ^ p) ≤
        D * (∑ i ∈ I, U i y ^ (2 / p)) ^ (p / 2) := by
    have h := hdec (fun i => glyzSliceSchwartz (f i) y)
      (fun i hi => glyzSlice_fourier_support_closed (f i) y (hΩ i hi) (hf i hi))
    simpa only [sum_apply, glyzSliceSchwartz_apply, U] using h
  rw [glyz_lintegral_withLp_eq_slices _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ y : V, D * (∑ i ∈ I, U i y ^ (2 / p)) ^ (p / 2) :=
      lintegral_mono hslice
    _ = D * ∫⁻ y : V, (∑ i ∈ I, U i y ^ (2 / p)) ^ (p / 2) :=
      lintegral_const_mul' _ _ hD
    _ ≤ D * (∑ i ∈ I, (∫⁻ y : V, U i y) ^ (2 / p)) ^ (p / 2) :=
      mul_le_mul_right (glyz_lintegral_mixed_l2 volume I U
        (fun i _ => (hU i).aemeasurable) hp) D
    _ = _ := by
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      exact (glyz_lintegral_withLp_eq_slices
        (fun z : WithLp 2 (H × V) => ‖f i z‖ₑ ^ p) (by fun_prop)).symm

/-- Recover the squared real norm estimate from the actual power
integrals. Schwartz integrability justifies all conversions. -/
theorem glyz_power_integrals_to_square_decoupling {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (I : Finset ℕ) (f : ℕ → SchwartzMap E ℂ) {p : ℝ≥0} (hp : 0 < p)
    {D : ℝ} (hD : 0 ≤ D)
    (h : (∫⁻ x, ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ)) ≤
      ENNReal.ofReal D ^ ((p : ℝ) / 2) *
        (∑ i ∈ I, (∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ)) ^ (2 / (p : ℝ))) ^ ((p : ℝ) / 2)) :
    lpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ) : E → ℂ) p volume ^ 2 ≤
      D * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ 2 := by
  have hp' : (0 : ℝ) < p := hp
  have hid (g : SchwartzMap E ℂ) :
      (∫⁻ x, ‖g x‖ₑ ^ (p : ℝ)) ^ (2 / (p : ℝ)) =
        ENNReal.ofReal (lpNorm (g : E → ℂ) p volume ^ (2 : ℕ)) := by
    rw [← eLpNorm_nnreal_pow_eq_lintegral hp.ne', ← ENNReal.rpow_mul,
      show (p : ℝ) * (2 / (p : ℝ)) = 2 by field_simp,
      ENNReal.rpow_two, ← ofReal_lpNorm (g.memLp p volume),
      ENNReal.ofReal_pow lpNorm_nonneg]
  have hpow := ENNReal.rpow_le_rpow h (show 0 ≤ 2 / (p : ℝ) by positivity)
  rw [hid, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (p : ℝ) / 2 * (2 / (p : ℝ)) = 1 by field_simp,
    ENNReal.rpow_one, ENNReal.rpow_one] at hpow
  simp only [hid] at hpow
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    ← ENNReal.ofReal_mul hD] at hpow
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hD
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))).mp hpow

/-- The lower-dimensional estimate lifts to a cylinder with exactly the
same real coefficient. -/
theorem glyz_cylindrical_square_decoupling
    (I : Finset ℕ) (Ω : ℕ → Set H) (hΩ : ∀ i ∈ I, IsClosed (Ω i))
    (f : ℕ → SchwartzMap (WithLp 2 (H × V)) ℂ)
    (hf : ∀ i ∈ I,
      Function.support (𝓕 (f i : WithLp 2 (H × V) → ℂ)) ⊆
        {z | (WithLp.ofLp z).1 ∈ Ω i})
    {p : ℝ≥0} (hp : 2 ≤ p) {D : ℝ} (hD : 0 ≤ D)
    (hdec : ∀ g : ℕ → SchwartzMap H ℂ,
      (∀ i ∈ I, Function.support (𝓕 (g i : H → ℂ)) ⊆ Ω i) →
      lpNorm ((∑ i ∈ I, g i : SchwartzMap H ℂ) : H → ℂ) p volume ^ 2 ≤
        D * ∑ i ∈ I, lpNorm (g i : H → ℂ) p volume ^ 2) :
    lpNorm ((∑ i ∈ I, f i : SchwartzMap (WithLp 2 (H × V)) ℂ) :
      WithLp 2 (H × V) → ℂ) p volume ^ 2 ≤
      D * ∑ i ∈ I, lpNorm (f i : WithLp 2 (H × V) → ℂ) p volume ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  apply glyz_power_integrals_to_square_decoupling I f hp0 hD
  apply glyz_cylindrical_power_decoupling I Ω hΩ f hf
    (show (2 : ℝ) ≤ p from hp) (ENNReal.ofReal D ^ ((p : ℝ) / 2))
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  intro g hg
  exact glyz_square_decoupling_to_power_integrals I g hp0 hD (hdec g hg)

end PlanarNikodym
