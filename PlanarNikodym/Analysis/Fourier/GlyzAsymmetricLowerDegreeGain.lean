import PlanarNikodym.Analysis.Fourier.GlyzDyadicLowerDegree
import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricRefinement
import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricLossTransfer
import PlanarNikodym.Analysis.Fourier.GlyzGainDepths
import PlanarNikodym.Analysis.Fourier.GlyzCriticalSignedDeviation

/-! GLYZ Lemma 3.9 for the genuine asymmetric constants. The lower-degree
gain comes from the actual transverse integral theorem, and both the
dyadic rounding and the passage to optimal losses are proved here. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace PlanarNikodym

theorem exists_uniform_glyz_asymmetric_lower_degree_gain
    (l r A : ℕ) (hr : 0 < r) (hA : l + r < A)
    (hQ : (l + r) * (l + r + 1) / 2 ≤ A)
    (a p : ℝ≥0) (ha : 2 ≤ a) (hap : a ≤ p)
    (hη : glyzOptimalSquareLoss l a = 0)
    (L : ℝ) (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N n m nb : ℕ), n ≤ m → m ≤ N → nb ≤ N →
      glyzDyadicScale nb ^ (r + 1) ≤ L * glyzDyadicScale m ^ l →
      glyzAsymmetricIntegralConstant (l + r) A N n nb p (a : ℝ) ≤
        C * (2 : ℝ) ^ (ε * m) *
          glyzAsymmetricIntegralConstant (l + r) A N m nb p (a : ℝ) := by
  obtain ⟨C, hC, hdec⟩ := exists_uniform_glyz_dyadic_lower_degree
    l r A hr hA hQ a ha hη L hL hε
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 2) ha
  have hp : 1 ≤ p := (by norm_num : (1 : ℝ≥0) ≤ 2).trans (ha.trans hap)
  refine ⟨C, hC, fun N n m nb hnm hmN hnbN hscale => ?_⟩
  have he : n + (m - n) = m := Nat.add_sub_of_le hnm
  have h := glyzAsymmetricIntegralConstant_le_of_refinement
    (N := N) (n := n) (n' := nb) (q := m - n) hA p hp
    (show (0 : ℝ) < a from ha0) (show (a : ℝ) ≤ p from hap)
    (D := C * (2 : ℝ) ^ (ε * m)) (by positivity)
    (by omega) (fun f hf i hi j hj hs => ?_)
  · simpa only [he] using h
  · apply glyz_asymmetric_refinement_real_of_ennreal hA p (ha0.trans_le hap)
      (show (0 : ℝ) < a from ha0) (show (a : ℝ) ≤ p from hap)
      (by positivity) f i j
    simpa only [he] using
      hdec N n m nb hnm hmN hnbN hscale f hf i hi j hj hs ((p : ℝ) - a)

theorem glyz_optimal_asymmetric_lower_degree_gain
    (l r A : ℕ) (hl : 0 < l) (hr : 0 < r) (hA : l + r < A)
    (hQ : (l + r) * (l + r + 1) / 2 ≤ A)
    (a p : ℝ≥0) (ha : 2 ≤ a) (hap : a ≤ p)
    (hη : glyzOptimalSquareLoss l a = 0)
    {α β : ℝ} (_hα : 0 ≤ α) (hαβ : α ≤ ((r : ℝ) + 1) / l * β)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hα'1 : ((r : ℝ) + 1) / l * β ≤ 1) :
    glyzOptimalAsymmetricLoss (l + r) A p (a : ℝ) α β ≤
      glyzOptimalAsymmetricLoss (l + r) A p (a : ℝ)
        (((r : ℝ) + 1) / l * β) β := by
  have hp : 1 ≤ p := (by norm_num : (1 : ℝ≥0) ≤ 2).trans (ha.trans hap)
  apply glyzOptimalAsymmetricLoss_le_of_small_loss_comparison hA p hp
    (show (0 : ℝ) ≤ a from a.coe_nonneg) (show (a : ℝ) ≤ p from hap)
  intro ε hε
  obtain ⟨C, hC, hgain⟩ := exists_uniform_glyz_asymmetric_lower_degree_gain
    l r A hr hA hQ a p ha hap hη ((2 : ℝ) ^ l) (by positivity) hε
  refine ⟨C, hC, fun N => ?_⟩
  have hnm := glyzDyadicDepth_mono N hαβ
  have hmN := glyzDyadicDepth_le (N := N) hα'1
  have hnbN := glyzDyadicDepth_le (N := N) hβ1
  have h := hgain N (glyzDyadicDepth N α)
    (glyzDyadicDepth N (((r : ℝ) + 1) / l * β)) (glyzDyadicDepth N β)
    hnm hmN hnbN (glyz_gain_inverse_radius_le l r N hl hβ.le)
  apply h.trans
  apply mul_le_mul_of_nonneg_right _
    (glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp a.coe_nonneg hap)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmN) hε.le

/-- The exact critical optimal-loss form of Lemma 3.9, ready for the
dimension induction. The only analytic premise is the lower-dimensional
ordinary moment theorem at its own critical exponent. -/
theorem glyz_critical_optimal_gain {k A l : ℕ}
    (hl : 0 < l) (hlk : l < k) (hA : k < A) (hQ : k * (k + 1) / 2 ≤ A)
    (hη : glyzOptimalSquareLoss l (glyzCriticalNNExponent l) = 0)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ glyzCriticalScaleRatio k l * β)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hα'1 : glyzCriticalScaleRatio k l * β ≤ 1) :
    glyzCriticalOptimalAsymmetricLoss k A l α β ≤
      glyzCriticalOptimalAsymmetricLoss k A l (glyzCriticalScaleRatio k l * β) β := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hlk.le
  have hr : 0 < r := by omega
  have ha : 2 ≤ glyzCriticalNNExponent l := by
    change (2 : ℝ) ≤ (l : ℝ) * ((l : ℝ) + 1)
    have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hap : glyzCriticalNNExponent l ≤ glyzCriticalNNExponent (l + r) :=
    glyzCriticalExponent_mono (by omega)
  have he : glyzCriticalScaleRatio (l + r) l = ((r : ℝ) + 1) / l := by
    simp [glyzCriticalScaleRatio]
  rw [he] at hαβ hα'1 ⊢
  exact glyz_optimal_asymmetric_lower_degree_gain l r A hl hr hA hQ
    (glyzCriticalNNExponent l) (glyzCriticalNNExponent (l + r)) ha hap hη hα hαβ hβ hβ1 hα'1

end PlanarNikodym
