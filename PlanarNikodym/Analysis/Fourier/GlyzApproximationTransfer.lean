import PlanarNikodym.Analysis.Fourier.GlyzConeLpLocalization

/-! Quantitative transfer from spectrally supported Schwartz approximants
to the original functions. Both the local error and the weighted right
side error are retained explicitly. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform
namespace PlanarNikodym

theorem glyz_enorm_rpow_le_of_approximation {p e : ℝ} (hp : 0 ≤ p)
    (z w : ℂ) (he : ‖z - w‖ ≤ e) :
    ‖z‖ₑ ^ p ≤ (2 : ℝ≥0∞) ^ p * (‖w‖ₑ ^ p + ENNReal.ofReal e ^ p) := by
  have he' : ‖z - w‖ₑ ≤ ENNReal.ofReal e := by
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal he
  have h : ‖z‖ₑ ≤ ‖w‖ₑ + ENNReal.ofReal e := by
    calc
      ‖z‖ₑ = ‖w + (z - w)‖ₑ := by congr 1; ring
      _ ≤ ‖w‖ₑ + ‖z - w‖ₑ := enorm_add_le _ _
      _ ≤ _ := add_le_add le_rfl he'
  exact (ENNReal.rpow_le_rpow h hp).trans
    (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp)

theorem glyz_weighted_power_le_of_approximation
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (g f : X → ℂ)
    (W : X → ℝ≥0∞) (hW : Measurable W) {p e : ℝ} (hp : 0 ≤ p)
    (he : ∀ x, ‖g x - f x‖ ≤ e) :
    (∫⁻ x, ‖g x‖ₑ ^ p * W x ∂μ) ≤ (2 : ℝ≥0∞) ^ p *
      ((∫⁻ x, ‖f x‖ₑ ^ p * W x ∂μ) + ENNReal.ofReal e ^ p * ∫⁻ x, W x ∂μ) := by
  have htwo : (2 : ℝ≥0∞) ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp (by norm_num)
  have hefin : ENNReal.ofReal e ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
  calc
    _ ≤ ∫⁻ x, (2 : ℝ≥0∞) ^ p *
        (‖f x‖ₑ ^ p * W x + ENNReal.ofReal e ^ p * W x) ∂μ := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ ((2 : ℝ≥0∞) ^ p * (‖f x‖ₑ ^ p + ENNReal.ofReal e ^ p)) * W x :=
          mul_le_mul_left (glyz_enorm_rpow_le_of_approximation hp _ _ (he x)) _
        _ = _ := by ring
    _ = _ := by
      rw [lintegral_const_mul' _ _ htwo,
        lintegral_add_right _ (measurable_const.mul hW),
        lintegral_const_mul' _ _ hefin]

theorem glyz_finite_approximation_transfer
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (g f : ι → X → ℂ) (e : ι → ℝ) (W : X → ℝ≥0∞) (hW : Measurable W)
    (U : Set X) {p : ℝ} (hp : 0 ≤ p) (D : ℝ≥0∞)
    (he : ∀ i ∈ s, ∀ x, ‖g i x - f i x‖ ≤ e i)
    (hdec : (∫⁻ x in U, ‖∑ i ∈ s, f i x‖ₑ ^ p ∂μ) ≤
      D * ∑ i ∈ s, ∫⁻ x, ‖f i x‖ₑ ^ p * W x ∂μ) :
    (∫⁻ x in U, ‖∑ i ∈ s, g i x‖ₑ ^ p ∂μ) ≤
      (2 : ℝ≥0∞) ^ p *
        (D * ((2 : ℝ≥0∞) ^ p *
          ((∑ i ∈ s, ∫⁻ x, ‖g i x‖ₑ ^ p * W x ∂μ) +
            (∑ i ∈ s, ENNReal.ofReal (e i) ^ p) * ∫⁻ x, W x ∂μ)) +
          ENNReal.ofReal (∑ i ∈ s, e i) ^ p * μ U) := by
  have hsum (x : X) : ‖(∑ i ∈ s, g i x) - ∑ i ∈ s, f i x‖ ≤ ∑ i ∈ s, e i := by
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => he i hi x)
  have hleft := glyz_weighted_power_le_of_approximation (μ.restrict U)
    (fun x => ∑ i ∈ s, g i x) (fun x => ∑ i ∈ s, f i x)
    (fun _ => 1) measurable_const hp hsum
  simp only [mul_one, lintegral_one, Measure.restrict_apply_univ] at hleft
  apply hleft.trans
  apply mul_le_mul_right
  refine add_le_add ?_ le_rfl
  apply hdec.trans
  apply mul_le_mul_right
  calc
    _ ≤ ∑ i ∈ s, (2 : ℝ≥0∞) ^ p *
        ((∫⁻ x, ‖g i x‖ₑ ^ p * W x ∂μ) + ENNReal.ofReal (e i) ^ p * ∫⁻ x, W x ∂μ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact glyz_weighted_power_le_of_approximation μ (f i) (g i) W hW hp
        (fun x => by simpa only [norm_sub_rev] using he i hi x)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]

/-- The constant and the sharp dyadic exponent come from the proved
cone theorem; no decoupling premise remains. The approximation errors
are explicit and may be supplied by the actual Fourier-tail construction. -/
theorem glyz_cone_approximate_local_lp (k A : ℕ) (hk : 0 < k)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B Q ε F rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q)
    (hε : 0 < ε) (hF : 0 < F) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (b : ℝ), 0 < b → b ≤ F * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (g : ℕ → GlyzConeSpace k → ℂ)
        (f : ℕ → SchwartzMap (GlyzConeSpace k) ℂ) (e : ℕ → ℝ) (a : GlyzConeSpace k),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzConeSpace k → ℂ)) ⊆
        glyzConeBox k γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      (∀ j ∈ I, ∀ x, ‖g j x - f j x‖ ≤ e j) →
      let W := fun x => ENNReal.ofReal (glyzNormWeight A (b • (x - a)))
      (∫⁻ x in closedBall a b⁻¹, ‖∑ i ∈ I, g i x‖ₑ ^ (p : ℝ)) ≤
        (2 : ℝ≥0∞) ^ (p : ℝ) *
          (ENNReal.ofReal (C * (2 : ℝ) ^
            (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
              ((2 : ℝ≥0∞) ^ (p : ℝ) *
                ((∑ i ∈ I, ∫⁻ x, ‖g i x‖ₑ ^ (p : ℝ) * W x) +
                  (∑ i ∈ I, ENNReal.ofReal (e i) ^ (p : ℝ)) * ∫⁻ x, W x)) +
            ENNReal.ofReal (∑ i ∈ I, e i) ^ (p : ℝ) * volume (closedBall a b⁻¹)) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_cone_translated_local_lp k A hk hp hβ hB hQ hε hF hrmin
  refine ⟨C, hC, fun γ hγ hder hdet N b hb hbδ I g f e a hI hf he => ?_⟩
  apply glyz_finite_approximation_transfer volume I g (fun i => f i) e _ ?_
    (closedBall a b⁻¹) p.coe_nonneg _ he
  · simpa only [sum_apply] using hlocal γ hγ hder hdet N b hb hbδ I f a hI hf
  · exact ENNReal.measurable_ofReal.comp (by
      unfold glyzNormWeight
      fun_prop)

end PlanarNikodym
