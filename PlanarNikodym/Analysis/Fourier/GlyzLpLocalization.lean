import PlanarNikodym.Analysis.Fourier.GlyzBandlimitedLocalization
import PlanarNikodym.Analysis.Fourier.GlyzSchwartzTranslation

/-! Genuine bandlimited localization for the ℓp form of decoupling.
The cutoff, its Fourier-support enlargement and the polynomial weight
are constructed. No localization hypothesis is retained. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators Pointwise
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_local_lp_of_bandlimited_cutoff
    {ι : Type*} (s : Finset ι) (f : ι → SchwartzMap E ℂ) (Ω : ι → Set E)
    (ψ : SchwartzMap E ℂ) (R S p : ℝ) (hp : 0 ≤ p)
    (W : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hf : ∀ i ∈ s, Function.support (𝓕 (f i : E → ℂ)) ⊆ Ω i)
    (hψ : ∀ x : E, ‖x‖ ≤ R → 1 ≤ ‖ψ x‖)
    (hsupp : Function.support (𝓕 (ψ : E → ℂ)) ⊆ closedBall (0 : E) S)
    (hweight : ∀ x, ‖ψ x‖ₑ ^ p ≤ W x)
    (hglobal : ∀ g : ι → SchwartzMap E ℂ,
      (∀ i ∈ s, Function.support (𝓕 (g i : E → ℂ)) ⊆ Ω i + closedBall (0 : E) S) →
      (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤ D * ∑ i ∈ s, ∫⁻ x, ‖g i x‖ₑ ^ p) :
    (∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤
      D * ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p * W x := by
  classical
  let g : ι → SchwartzMap E ℂ := fun i =>
    SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (f i) ψ
  have hgsupp (i : ι) (hi : i ∈ s) :
      Function.support (𝓕 (g i : E → ℂ)) ⊆ Ω i + closedBall (0 : E) S :=
    (support_fourier_glyz_schwartz_product (f i) ψ).trans (add_subset_add (hf i hi) hsupp)
  have hsum (x : E) : (∑ i ∈ s, g i) x = (∑ i ∈ s, f i) x * ψ x := by
    simp [g, Finset.sum_mul]
  calc
    _ ≤ ∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, g i) x‖ₑ ^ p := by
      apply setLIntegral_mono' measurableSet_closedBall
      intro x hx
      have hψx : (1 : ℝ≥0∞) ≤ ‖ψ x‖ₑ := by
        simpa only [ENNReal.ofReal_one, ofReal_norm] using ENNReal.ofReal_le_ofReal
          (hψ x (by simpa only [mem_closedBall, dist_zero_right] using hx))
      rw [hsum, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp]
      exact le_mul_of_one_le_right' (by simpa using ENNReal.rpow_le_rpow hψx hp)
    _ ≤ ∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p := lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ D * ∑ i ∈ s, ∫⁻ x, ‖g i x‖ₑ ^ p := hglobal g hgsupp
    _ ≤ _ := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro i hi
      apply lintegral_mono
      intro x
      change ‖f i x * ψ x‖ₑ ^ p ≤ _
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp]
      exact mul_le_mul_right (hweight x) _

/-- Uniform in the spatial radius, frequency sets, finite family, and
global coefficient. The right side is the actual sum of weighted integrals. -/
theorem exists_glyz_global_to_weighted_local_lp (A : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ S C : ℝ, 0 < S ∧ 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (ι : Type*) (s : Finset ι) (f : ι → SchwartzMap E ℂ)
      (Ω : ι → Set E) (D : ℝ≥0∞),
      (∀ i ∈ s, Function.support (𝓕 (f i : E → ℂ)) ⊆ Ω i) →
      (∀ g : ι → SchwartzMap E ℂ,
        (∀ i ∈ s, Function.support (𝓕 (g i : E → ℂ)) ⊆
          Ω i + closedBall (0 : E) (S / R)) →
        (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤
          D * ∑ i ∈ s, ∫⁻ x, ‖g i x‖ₑ ^ p) →
      (∫⁻ x in closedBall (0 : E) R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤
        D * ENNReal.ofReal C *
          ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p *
            ENNReal.ofReal (glyzNormWeight A (R⁻¹ • x)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨S, hS, hcut⟩ := exists_glyz_bandlimited_cutoffs (E := E)
  obtain ⟨C, hC, hcut⟩ := hcut A
  refine ⟨S, C ^ p, hS, Real.rpow_pos_of_pos hC _, fun R hR ι s f Ω D hf hglobal => ?_⟩
  obtain ⟨ψ, hlower, hsupp, hdecay⟩ := hcut R hR
  let c := ENNReal.ofReal C ^ p
  let w : E → ℝ≥0∞ := fun x => ENNReal.ofReal (glyzNormWeight A (R⁻¹ • x))
  have hc : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have hweight (x : E) : ‖ψ x‖ₑ ^ p ≤ c * w x := by
    have hw1 : w x ≤ 1 := by
      apply ENNReal.ofReal_le_one.mpr
      change (max (1 : ℝ) ‖R⁻¹ • x‖ ^ A)⁻¹ ≤ 1
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left _ _))
    calc
      _ ≤ ENNReal.ofReal (C * glyzNormWeight A (R⁻¹ • x)) ^ p :=
        ENNReal.rpow_le_rpow (by
          simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hdecay x)) hp0.le
      _ = c * w x ^ p := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      _ ≤ _ := mul_le_mul_right (ENNReal.rpow_le_self_of_le_one hw1 hp) _
  have h := glyz_local_lp_of_bandlimited_cutoff s f Ω ψ R (S / R) p hp0.le
    (fun x => c * w x) D hf hlower hsupp hweight hglobal
  have hi (i : ι) : (∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)) =
      c * ∫⁻ x, ‖f i x‖ₑ ^ p * w x := by
    simp_rw [mul_left_comm (‖f i _‖ₑ ^ p) c]
    exact lintegral_const_mul' _ _ hc
  simp_rw [hi] at h
  rw [← Finset.mul_sum] at h
  have he : c = ENNReal.ofReal (C ^ p) := ENNReal.ofReal_rpow_of_nonneg hC.le hp0.le
  simpa only [he, mul_assoc, w] using h

/-- Flexible physical radii for derivative-scaled boxes. The inverse
radius may be any positive number below a fixed multiple of δ^l. -/
theorem exists_glyz_scaled_boxes_flexible_local_lp (l A : ℕ)
    {p : ℝ} (hp : 1 ≤ p) (F : ℝ) :
    ∃ S C : ℝ, 0 < S ∧ 0 < C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ∀ (b : ℝ), 0 < b → b ≤ F * δ ^ l →
      ∀ (K T : ℝ), 0 ≤ K → ∀ (ι : Type*) (s : Finset ι)
      (L : ι → GlyzSpace l ≃L[ℝ] GlyzSpace l) (a : ι → GlyzSpace l)
      (f : ι → SchwartzMap (GlyzSpace l) ℂ) (D : ℝ≥0∞),
      (∀ i ∈ s, ‖(L i).symm.toContinuousLinearMap‖ ≤ K) →
      (∀ i ∈ s, Function.support (𝓕 (f i : GlyzSpace l → ℂ)) ⊆
        glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) T) →
      (∀ g : ι → SchwartzMap (GlyzSpace l) ℂ,
        (∀ i ∈ s, Function.support (𝓕 (g i : GlyzSpace l → ℂ)) ⊆
          glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) (T + K * (S * F))) →
        (∫⁻ x, ‖(∑ i ∈ s, g i) x‖ₑ ^ p) ≤ D * ∑ i ∈ s, ∫⁻ x, ‖g i x‖ₑ ^ p) →
      (∫⁻ x in closedBall (0 : GlyzSpace l) b⁻¹, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤
        D * ENNReal.ofReal C *
          ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p *
            ENNReal.ofReal (glyzNormWeight A (b • x)) := by
  obtain ⟨S, C, hS, hC, hlocal⟩ :=
    exists_glyz_global_to_weighted_local_lp (E := GlyzSpace l) A hp
  refine ⟨S, C, hS, hC, fun δ hδ hδ1 b hb hbδ K T hK ι s L a f D hL hf hglobal => ?_⟩
  have h := hlocal b⁻¹ (inv_pos.mpr hb) ι s f
    (fun i => glyzFrequencyBox (glyzScaledFrame (L i) δ hδ) (a i) T) D hf ?_
  · simpa only [inv_inv] using h
  · intro g hg
    apply hglobal g
    intro i hi
    apply (hg i hi).trans
    rw [div_inv_eq_mul]
    exact (add_subset_add (Subset.refl _) (closedBall_subset_closedBall
      (show S * b ≤ (S * F) * δ ^ l by nlinarith))).trans
        (glyz_scaled_box_add_ball_subset (L i) hδ hδ1 hK (hL i hi) (a i))

/-- The local ℓp estimate has the same coefficient after normalizing
both the ball measure and every weighted piece by the ball volume. -/
theorem glyz_normalize_centered_local_lp {ι : Type*} (s : Finset ι)
    (f : ι → SchwartzMap E ℂ) (a : E) {R p : ℝ} (hR : 0 < R)
    (w : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hlocal : (∫⁻ x in closedBall a R, ‖(∑ i ∈ s, f i) x‖ₑ ^ p) ≤
      D * ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p * w x) :
    (∫⁻ x, ‖(∑ i ∈ s, f i) x‖ₑ ^ p ∂glyzCenteredBallMeasure a R) ≤
      D * ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p *
        ((volume (closedBall a R))⁻¹ * w x) := by
  let c : ℝ≥0∞ := (volume (closedBall a R))⁻¹
  have hc : c ≠ ⊤ := ENNReal.inv_ne_top.mpr (measure_closedBall_pos volume a hR).ne'
  have hi (i : ι) : (∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)) =
      c * ∫⁻ x, ‖f i x‖ₑ ^ p * w x := by
    simp_rw [mul_left_comm (‖f i _‖ₑ ^ p) c]
    exact lintegral_const_mul' _ _ hc
  change _ ≤ D * ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p * (c * w x)
  simp_rw [hi]
  rw [← Finset.mul_sum, glyzCenteredBallMeasure, lintegral_smul_measure, smul_eq_mul]
  change c * _ ≤ D * (c * _)
  calc
    _ ≤ c * (D * ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p * w x) := mul_le_mul_right hlocal c
    _ = _ := by ring

end PlanarNikodym
