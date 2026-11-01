import PlanarNikodym.Analysis.Fourier.GlyzSupercriticalCone
import PlanarNikodym.Analysis.Fourier.GlyzConeThickening
import PlanarNikodym.Analysis.Fourier.GlyzLpLocalization
import PlanarNikodym.Analysis.Fourier.GlyzTranslatedCurveLocalization

/-! Local weighted cone decoupling with the sharp high-p power.
A fixed enlargement of the physical cutoff ensures its Fourier thickening
stays in a positive radial region at every angular depth. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform NNReal ENNReal BigOperators Pointwise
namespace PlanarNikodym

theorem glyzNormWeight_dilation_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℕ) {T : ℝ} (hT : 1 ≤ T) (x : E) :
    glyzNormWeight A (T⁻¹ • x) ≤ T ^ A * glyzNormWeight A x := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hmax : max (1 : ℝ) ‖x‖ ≤ T * max 1 ‖T⁻¹ • x‖ := by
    apply max_le
    · exact hT.trans (le_mul_of_one_le_right hT0.le (le_max_left _ _))
    · calc
        ‖x‖ = T * ‖T⁻¹ • x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT0),
            ← mul_assoc, mul_inv_cancel₀ hT0.ne', one_mul]
        _ ≤ T * max 1 ‖T⁻¹ • x‖ := mul_le_mul_of_nonneg_left (le_max_right _ _) hT0.le
  change (max 1 ‖T⁻¹ • x‖ ^ A)⁻¹ ≤ T ^ A * (max 1 ‖x‖ ^ A)⁻¹
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul, mul_pow] using pow_le_pow_left₀ (by positivity) hmax A

theorem glyz_cone_local_lp (k A : ℕ) (hk : 0 < k)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B Q ε F rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q)
    (hε : 0 < ε) (hF : 0 < F) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (b : ℝ), 0 < b → b ≤ F * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace k) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzConeSpace k → ℂ)) ⊆
        glyzConeBox k γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      (∫⁻ x in closedBall (0 : GlyzConeSpace k) b⁻¹, ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
          ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • x)) := by
  have hp1 : (1 : ℝ) ≤ p := (show (1 : ℝ≥0) ≤ p from
    (one_le_glyzCriticalNNExponent hk).trans hp)
  obtain ⟨S, C₀, hS, hC₀, hlocal⟩ :=
    exists_glyz_global_to_weighted_local_lp (E := GlyzConeSpace k) A hp1
  let τ := rmin / 2
  have hτ : 0 < τ := half_pos hrmin
  obtain ⟨Q', hQ', hthick⟩ := exists_uniform_glyz_cone_thickening k hβ hB hQ hτ hrmin
  obtain ⟨C₁, hC₁, hglobal⟩ := glyz_supercritical_cone_subset_power_decoupling k hk hp
    hβ hB hQ' hε (half_pos hrmin) (rmax := rmax + rmin / 2)
  let T := max 1 (S * F / τ)
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT : 0 < T := zero_lt_one.trans_le hT1
  refine ⟨C₁ * C₀ * T ^ A, by positivity, fun γ hγ hder hdet N b hb hbδ I f hI hf => ?_⟩
  let δ := glyzDyadicScale N
  have hδ : 0 < δ := glyzDyadicScale_pos N
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hsmall : τ * δ ^ k ≤ rmin / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_one₀ hδ.le hδ1) hτ.le).trans_eq (mul_one τ)
  have hTf : S * F ≤ T * τ := (div_le_iff₀ hτ).mp (le_max_right _ _)
  have hfreq : S / (T / b) ≤ τ * δ ^ k := by
    have he : S / (T / b) = S * b / T := by field_simp
    rw [he, div_le_iff₀ hT]
    calc
      S * b ≤ S * (F * δ ^ k) := mul_le_mul_of_nonneg_left hbδ hS.le
      _ ≤ (T * τ) * δ ^ k := by nlinarith [pow_nonneg hδ.le k]
      _ = _ := by ring
  let D := ENNReal.ofReal (C₁ * (2 : ℝ) ^
    (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N))
  have h := hlocal (T / b) (div_pos hT hb) ℕ I f
    (fun i => glyzConeBox k γ (glyzDyadicCenter N i) δ Q rmin rmax) D hf (by
      intro g hg
      apply hglobal γ hγ hder hdet N I g hI
      intro i hi
      apply (hg i hi).trans
      apply (add_subset_add (Subset.refl _) (closedBall_subset_closedBall hfreq)).trans
      exact hthick γ (glyzDyadicCenter N i) δ rmax hδ hδ1 hsmall
        (fun j hj => hder _ (glyzDyadicCenter_mem_Icc (Finset.mem_range.mp (hI hi))) j (by omega))
        (hdet _ (glyzDyadicCenter_mem_Icc (Finset.mem_range.mp (hI hi)))))
  have hw (x : GlyzConeSpace k) :
      glyzNormWeight A ((T / b)⁻¹ • x) ≤ T ^ A * glyzNormWeight A (b • x) := by
    have he : (T / b)⁻¹ = T⁻¹ * b := by field_simp
    rw [he, ← smul_smul]
    exact glyzNormWeight_dilation_le A hT1 (b • x)
  have hwi (i : ℕ) :
      (∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A ((T / b)⁻¹ • x))) ≤
        ENNReal.ofReal (T ^ A) *
          ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A (b • x)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    calc
      _ ≤ ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (T ^ A * glyzNormWeight A (b • x)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal (hw x)) _
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ring
  calc
    _ ≤ ∫⁻ x in closedBall (0 : GlyzConeSpace k) (T / b), ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ) :=
      lintegral_mono_set (closedBall_subset_closedBall (by
        rw [← one_div]
        exact div_le_div_of_nonneg_right hT1 hb.le))
    _ ≤ D * ENNReal.ofReal C₀ *
        ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A ((T / b)⁻¹ • x)) := h
    _ ≤ D * ENNReal.ofReal C₀ * (ENNReal.ofReal (T ^ A) *
        ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) * ENNReal.ofReal (glyzNormWeight A (b • x))) := by
      apply mul_le_mul_right
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hwi i
    _ = _ := by
      dsimp [D]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

theorem glyz_cone_translated_local_lp (k A : ℕ) (hk : 0 < k)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent k ≤ p)
    {β B Q ε F rmin rmax : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q)
    (hε : 0 < ε) (hF : 0 < F) (hrmin : 0 < rmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (b : ℝ), 0 < b → b ≤ F * glyzDyadicScale N ^ k →
      ∀ (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace k) ℂ) (a : GlyzConeSpace k),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzConeSpace k → ℂ)) ⊆
        glyzConeBox k γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q rmin rmax) →
      (∫⁻ x in closedBall a b⁻¹, ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent k / 2 - 1 + ε) * N)) *
          ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • (x - a))) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_cone_local_lp k A hk hp hβ hB hQ hε hF hrmin
  refine ⟨C, hC, fun γ hγ hder hdet N b hb hbδ I f a hI hf => ?_⟩
  have h := hlocal γ hγ hder hdet N b hb hbδ I
    (fun i => glyzSchwartzTranslate a (f i)) hI (by
      intro i hi
      rw [support_fourier_glyzSchwartzTranslate]
      exact hf i hi)
  rw [← glyzSchwartzTranslate_sum] at h
  simp_rw [glyz_lintegral_schwartz_translate_weight] at h
  simp only [glyzSchwartzTranslate_apply] at h
  rwa [glyz_lintegral_closedBall_translate a b⁻¹
    (fun x => ‖(∑ i ∈ I, f i) x‖ₑ ^ (p : ℝ))] at h

end PlanarNikodym
