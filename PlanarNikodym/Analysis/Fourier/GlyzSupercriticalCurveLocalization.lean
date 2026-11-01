import PlanarNikodym.Analysis.Fourier.GlyzSupercriticalCurve
import PlanarNikodym.Analysis.Fourier.GlyzLpLocalization

/-! Actual weighted local high-p decoupling for general curves, with
uniform constants before the curve, angular depth, and physical ball. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_supercritical_curve_subset_power_decoupling (m : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ),
      I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace m → ℂ)) ⊆
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x, ‖(∑ i ∈ I, f i : SchwartzMap (GlyzSpace m) ℂ) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) *
            ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) := by
  classical
  obtain ⟨C, hC, hglobal⟩ := glyz_supercritical_curve_power_decoupling m hm hp hβ hB hQ hε
  refine ⟨C, hC, fun γ hγ hder hdet N I f hI hf => ?_⟩
  let g : ℕ → SchwartzMap (GlyzSpace m) ℂ := fun j => if j ∈ I then f j else 0
  have hgsupp : ∀ j < 2 ^ N, Function.support (𝓕 (g j : GlyzSpace m → ℂ)) ⊆
      glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q := by
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
  have hp0 : (0 : ℝ) < p := (glyzCriticalExponent_pos hm).trans_le (show _ ≤ (p : ℝ) from hp)
  have henergy : (∑ j ∈ Finset.range (2 ^ N), ∫⁻ x, ‖g j x‖ₑ ^ (p : ℝ)) =
      ∑ j ∈ I, ∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) := by
    calc
      _ = ∑ j ∈ I, ∫⁻ x, ‖g j x‖ₑ ^ (p : ℝ) :=
        (Finset.sum_subset hI (fun j _ hj => by simp [g, hj, ENNReal.zero_rpow_of_pos hp0])).symm
      _ = _ := Finset.sum_congr rfl fun j hj => by simp only [g, if_pos hj]
  have h := hglobal γ hγ hder hdet N g hgsupp
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) p.coe_nonneg, ofReal_norm] at h
  simpa only [hsum, henergy] using h

theorem glyz_supercritical_curve_flexible_local (m A : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ m → I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace m → ℂ)) ⊆
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall (0 : GlyzSpace m) b⁻¹,
        ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) *
          ∑ j ∈ I, ∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • x)) := by
  classical
  have hp1 : 1 ≤ p := (one_le_glyzCriticalNNExponent hm).trans hp
  obtain ⟨K, hK, hframe⟩ := exists_uniform_glyz_general_curve_inverse m hβ hB
  obtain ⟨S, C₀, hS, hC₀, hlocal⟩ := exists_glyz_scaled_boxes_flexible_local_lp m A (show (1 : ℝ) ≤ p from hp1) F
  have hQ' : 0 < Q + K * (S * F) := by positivity
  obtain ⟨D, hD, hglobal⟩ := glyz_supercritical_curve_subset_power_decoupling m hm hp hβ hB hQ' hε
  refine ⟨D * C₀, mul_pos hD hC₀, fun γ hγ hder hdet N I f b hb hbδ hI hf => ?_⟩
  have hδ := glyzDyadicScale_pos N
  have hδ1 : glyzDyadicScale N ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hframes (j : ℕ) : ∃ L : GlyzSpace m ≃L[ℝ] GlyzSpace m,
      j ∈ I → L.toContinuousLinearMap = glyzCurveJetOperator γ (glyzDyadicCenter N j) ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ K := by
    by_cases hj : j ∈ I
    · have hjunit := glyzDyadicCenter_mem_Icc (Finset.mem_range.mp (hI hj))
      obtain ⟨L, hL, hnorm⟩ := hframe γ (glyzDyadicCenter N j)
        (fun u => hder _ hjunit (u + 1) (by omega)) (hdet _ hjunit)
      exact ⟨L, fun _ => ⟨hL, hnorm⟩⟩
    · exact ⟨ContinuousLinearEquiv.refl ℝ _, fun hj' => False.elim (hj hj')⟩
  choose L hL using hframes
  have hbox (j : ℕ) (hj : j ∈ I) (T : ℝ) (hT : 0 ≤ T) :
      glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) T =
      glyzFrequencyBox (glyzScaledFrame (L j) (glyzDyadicScale N) hδ)
        (γ (glyzDyadicCenter N j)) T :=
    glyzEnlargedCurveBox_eq_frequencyBox _ _ _ _ hδ hT (L j) (hL j hj).1
  have h := hlocal (glyzDyadicScale N) hδ hδ1 b hb hbδ K Q hK.le ℕ I L
    (fun j => γ (glyzDyadicCenter N j)) f
    (ENNReal.ofReal (D * (2 : ℝ) ^ (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)))
    (fun j hj => (hL j hj).2)
    (fun j hj => by rw [← hbox j hj Q hQ.le]; exact hf j hj) (by
      intro g hg
      exact hglobal γ hγ hder hdet N I g hI (fun j hj => by
        rw [hbox j hj _ hQ'.le]; exact hg j hj))
  rw [← ENNReal.ofReal_mul (by positivity)] at h
  have hc : (D * (2 : ℝ) ^ (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) * C₀ =
      (D * C₀) * (2 : ℝ) ^ (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N) := by ring
  rwa [hc] at h

theorem glyz_supercritical_curve_translated_local (m A : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ)
      (a : GlyzSpace m) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ m → I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace m → ℂ)) ⊆
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x in closedBall a b⁻¹, ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ)) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) *
          ∑ j ∈ I, ∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ENNReal.ofReal (glyzNormWeight A (b • (x - a))) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_supercritical_curve_flexible_local m A hm hp F hF hβ hB hQ hε
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

theorem glyz_supercritical_curve_normalized_local (m A : ℕ) (hm : 0 < m)
    {p : ℝ≥0} (hp : glyzCriticalNNExponent m ≤ p) (F : ℝ) (hF : 0 < F)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace m,
      ContDiff ℝ (m + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ m + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (I : Finset ℕ) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ)
      (a : GlyzSpace m) (b : ℝ),
      0 < b → b ≤ F * glyzDyadicScale N ^ m → I ⊆ Finset.range (2 ^ N) →
      (∀ j ∈ I, Function.support (𝓕 (f j : GlyzSpace m → ℂ)) ⊆
        glyzEnlargedCurveBox γ m (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      (∫⁻ x, ‖(∑ j ∈ I, f j) x‖ₑ ^ (p : ℝ) ∂glyzCenteredBallMeasure a b⁻¹) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^
          (((p : ℝ) - glyzCriticalExponent m / 2 - 1 + ε) * N)) *
          ∑ j ∈ I, ∫⁻ x, ‖f j x‖ₑ ^ (p : ℝ) *
            ((volume (closedBall a b⁻¹))⁻¹ * ENNReal.ofReal (glyzNormWeight A (b • (x - a)))) := by
  obtain ⟨C, hC, hlocal⟩ := glyz_supercritical_curve_translated_local m A hm hp F hF hβ hB hQ hε
  refine ⟨C, hC, fun γ hγ hder hdet N I f a b hb hbδ hI hf => ?_⟩
  exact glyz_normalize_centered_local_lp I f a (inv_pos.mpr hb) _ _
    (hlocal γ hγ hder hdet N I f a b hb hbδ hI hf)

end PlanarNikodym
