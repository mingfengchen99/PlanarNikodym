import PlanarNikodym.Analysis.Fourier.GlyzGeneralCurveDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzFlexibleCurveLocalization
import PlanarNikodym.Analysis.Fourier.GlyzSchwartzTranslation

/-! Uniform weighted localization for the full finite-regularity curve class.
All curve dependence is controlled by actual derivative and determinant bounds. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_general_curve_subset_decoupling_of_moment_optimal_zero
    (l : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((∑ j ∈ I, f j : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) p volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) *
          ∑ j ∈ I, lpNorm (f j : GlyzSpace l → ℂ) p volume ^ 2 := by
  classical
  obtain ⟨C, hC, hglobal⟩ :=
    glyz_general_curve_decoupling_of_moment_optimal_zero l hp hη hβ hB hQ hε
  refine ⟨C, hC, fun γ hγ hder hdet N I f hI hf => ?_⟩
  let g : ℕ → SchwartzMap (GlyzSpace l) ℂ := fun j => if j ∈ I then f j else 0
  have hgsupp : ∀ j < 2 ^ N, Function.support (𝓕 (g j : GlyzSpace l → ℂ)) ⊆
      glyzEnlargedCurveBox γ l
        (glyzDyadicCenter N j) (glyzDyadicScale N) Q := by
    intro j _
    by_cases hjI : j ∈ I
    · simpa only [g, if_pos hjI] using hf j hjI
    · simp only [g, if_neg hjI]
      rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_zero]
      simp only [FunLike.coe_zero, Function.support_zero, empty_subset]
  have hsum : (∑ j ∈ Finset.range (2 ^ N), g j) = ∑ j ∈ I, f j := by
    calc
      _ = ∑ j ∈ I, g j := (Finset.sum_subset hI (fun j _ hj => by simp [g, hj])).symm
      _ = _ := Finset.sum_congr rfl fun j hj => by simp only [g, if_pos hj]
  have henergy : (∑ j ∈ Finset.range (2 ^ N), lpNorm (g j : GlyzSpace l → ℂ) p volume ^ 2) =
      ∑ j ∈ I, lpNorm (f j : GlyzSpace l → ℂ) p volume ^ 2 := by
    calc
      _ = ∑ j ∈ I, lpNorm (g j : GlyzSpace l → ℂ) p volume ^ 2 :=
        (Finset.sum_subset hI (fun j _ hj => by
          simp only [g, if_neg hj, FunLike.coe_zero, lpNorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])).symm
      _ = _ := Finset.sum_congr rfl fun j hj => by simp only [g, if_pos hj]
  simpa only [hsum, henergy] using hglobal γ hγ hder hdet N g hgsupp

theorem glyz_general_curve_flexible_local_of_moment_optimal_zero
    (l A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ l →
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall (0 : GlyzSpace l) b⁻¹,
        ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • x))) ^
              (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  classical
  have hpR : (1 : ℝ) ≤ p := hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hpR
  obtain ⟨K, hK, hframe⟩ := exists_uniform_glyz_general_curve_inverse l hβ hB
  obtain ⟨S, C₀, hS, hC₀, hlocal⟩ := exists_glyz_scaled_boxes_flexible_local_decoupling l A hpR F hF
  let α : ℝ := 2 * ε / p
  have hα : 0 < α := by dsimp [α]; positivity
  have hQ' : 0 < Q + K * (S * F) := by positivity
  obtain ⟨D, hD, hglobal⟩ := glyz_general_curve_subset_decoupling_of_moment_optimal_zero
    l hp hη hβ hB hQ' hα
  refine ⟨D ^ ((p : ℝ) / 2) * C₀, mul_pos (Real.rpow_pos_of_pos hD _) hC₀,
    fun γ hγ hder hdet N I f b hb hbδ hI hf => ?_⟩
  have hδ := glyzDyadicScale_pos N
  have hδ1 : glyzDyadicScale N ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hframes (j : ℕ) : ∃ L : GlyzSpace l ≃L[ℝ] GlyzSpace l,
      j ∈ I → L.toContinuousLinearMap =
        glyzCurveJetOperator γ (glyzDyadicCenter N j) ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ K := by
    by_cases hj : j ∈ I
    · have hjunit := glyzDyadicCenter_mem_Icc (Finset.mem_range.mp (hI hj))
      obtain ⟨L, hL, hnorm⟩ := hframe γ (glyzDyadicCenter N j)
        (fun u => hder _ hjunit (u + 1) (by omega)) (hdet _ hjunit)
      exact ⟨L, fun _ => ⟨hL, hnorm⟩⟩
    · exact ⟨ContinuousLinearEquiv.refl ℝ (GlyzSpace l), fun hj' => False.elim (hj hj')⟩
  choose L hL using hframes
  have hbox (j : ℕ) (hj : j ∈ I) (T : ℝ) (hT : 0 ≤ T) :
      glyzEnlargedCurveBox γ l
        (glyzDyadicCenter N j) (glyzDyadicScale N) T =
      glyzFrequencyBox (glyzScaledFrame (L j) (glyzDyadicScale N) hδ)
        (γ (glyzDyadicCenter N j)) T :=
    glyzEnlargedCurveBox_eq_frequencyBox _ _ _ _ hδ hT (L j) (hL j hj).1
  have h := hlocal (glyzDyadicScale N) hδ hδ1 b hb hbδ K Q hK.le ℕ I L
    (fun j => γ (glyzDyadicCenter N j)) f
    (ENNReal.ofReal (D * (2 : ℝ) ^ (α * N)) ^ ((p : ℝ) / 2))
    (fun j hj => (hL j hj).2)
    (fun j hj => by rw [← hbox j hj Q hQ.le]; exact hf j hj) (by
      intro g hg
      have hbound := hglobal γ hγ hder hdet N I g hI (fun j hj => by
        rw [hbox j hj (Q + K * (S * F)) hQ'.le]
        exact hg j hj)
      exact glyz_square_decoupling_to_power_integrals I g
        (show 0 < p from hp0) (by positivity) hbound)
  have hcoef : ENNReal.ofReal (D * (2 : ℝ) ^ (α * N)) ^ ((p : ℝ) / 2) *
      ENNReal.ofReal C₀ =
      ENNReal.ofReal ((D ^ ((p : ℝ) / 2) * C₀) * (2 : ℝ) ^ (ε * N)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ D * (2 : ℝ) ^ (α * N))
      (by positivity : 0 ≤ (p : ℝ) / 2),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hD.le (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : (α * (N : ℝ)) * ((p : ℝ) / 2) = ε * N := by
      dsimp [α]
      field_simp [hp0.ne']
    rw [he]
    ring
  simpa only [hcoef] using h


/-- Flexible local estimate on a ball about any physical center, uniformly
over the finite-regularity curve class. -/
theorem glyz_general_curve_translated_local_of_moment_optimal_zero
    (l A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (a : GlyzSpace l) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ l →
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall a b⁻¹,
        ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • (x - a)))) ^
              (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_general_curve_flexible_local_of_moment_optimal_zero
    l A hp hη F hF hβ hB hQ hε
  refine ⟨C, hC, fun γ hγ hder hdet N I f a b hb hbδ hI hf => ?_⟩
  have h := hlocal γ hγ hder hdet N I (fun j => glyzSchwartzTranslate a (f j)) b hb hbδ hI (by
    intro j hj
    rw [support_fourier_glyzSchwartzTranslate]
    exact hf j hj)
  rw [← glyzSchwartzTranslate_sum] at h
  simp_rw [glyz_lintegral_schwartz_translate_weight] at h
  simp only [glyzSchwartzTranslate_apply] at h
  rw [glyz_lintegral_closedBall_translate a b⁻¹
    (fun x => ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ))] at h
  exact h

/-- Volume-normalized version on any physical ball. The translated
weight is normalized by the volume of that same ball. -/
theorem glyz_general_curve_translated_normalized_local_of_moment_optimal_zero
    (l A : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (a : GlyzSpace l) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ l →
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x, ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)
        ∂glyzCenteredBallMeasure a b⁻¹) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ((volume (closedBall a b⁻¹))⁻¹ *
              ENNReal.ofReal (glyzNormWeight A (b • (x - a))))) ^
                (2 / (p : ℝ))) ^ ((p : ℝ) / 2) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_general_curve_translated_local_of_moment_optimal_zero
    l A hp hη F hF hβ hB hQ hε
  refine ⟨C, hC, fun γ hγ hder hdet N I f a b hb hbδ hI hf => ?_⟩
  exact glyz_normalize_centered_local_decoupling I f a
    (inv_pos.mpr hb)
    (by exact_mod_cast lt_of_lt_of_le zero_lt_one hp) _ _
    (hlocal γ hγ hder hdet N I f a b hb hbδ hI hf)

/-- The critical estimate with the proved moment theorem substituted. -/
theorem glyz_general_curve_subset_decoupling_critical
    (l : ℕ) (hl : 0 < l)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((∑ j ∈ I, f j : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) (glyzCriticalNNExponent l) volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) *
          ∑ j ∈ I, lpNorm (f j : GlyzSpace l → ℂ) (glyzCriticalNNExponent l) volume ^ 2 :=
  glyz_general_curve_subset_decoupling_of_moment_optimal_zero
    l (one_le_glyzCriticalNNExponent hl) (glyz_critical_optimal_square_loss_eq_zero l hl) hβ hB hQ hε

/-- The critical estimate with the proved moment theorem substituted. -/
theorem glyz_general_curve_translated_local_critical
    (l A : ℕ) (hl : 0 < l) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (a : GlyzSpace l) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ l →
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall a b⁻¹,
        ‖(∑ j ∈ I, f j) x‖ₑ ^ ((glyzCriticalNNExponent l : ℝ≥0) : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ ((glyzCriticalNNExponent l : ℝ≥0) : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • (x - a)))) ^
              (2 / ((glyzCriticalNNExponent l : ℝ≥0) : ℝ))) ^ (((glyzCriticalNNExponent l : ℝ≥0) : ℝ) / 2) :=
  glyz_general_curve_translated_local_of_moment_optimal_zero
    l A (one_le_glyzCriticalNNExponent hl) (glyz_critical_optimal_square_loss_eq_zero l hl) F hF hβ hB hQ hε

/-- The critical estimate with the proved moment theorem substituted. -/
theorem glyz_general_curve_translated_normalized_local_critical
    (l A : ℕ) (hl : 0 < l) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ) (a : GlyzSpace l) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ l →
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x, ‖(∑ j ∈ I, f j) x‖ₑ ^ ((glyzCriticalNNExponent l : ℝ≥0) : ℝ)
        ∂glyzCenteredBallMeasure a b⁻¹) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (ε * N)) *
          (∑ j ∈ I, (∫⁻ x, ‖f j x‖ₑ ^ ((glyzCriticalNNExponent l : ℝ≥0) : ℝ) *
            ((volume (closedBall a b⁻¹))⁻¹ *
              ENNReal.ofReal (glyzNormWeight A (b • (x - a))))) ^
                (2 / ((glyzCriticalNNExponent l : ℝ≥0) : ℝ))) ^ (((glyzCriticalNNExponent l : ℝ≥0) : ℝ) / 2) :=
  glyz_general_curve_translated_normalized_local_of_moment_optimal_zero
    l A (one_le_glyzCriticalNNExponent hl) (glyz_critical_optimal_square_loss_eq_zero l hl) F hF hβ hB hQ hε

end PlanarNikodym
