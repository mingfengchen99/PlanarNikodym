import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricReverseComparison
import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricInterpolation
import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricSymmetry

/-! Symmetrization of the actual coarse asymmetric comparison. The
result is the integral form of GLYZ Lemma 3.4, with no unproved
decoupling inequality among its assumptions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyz_ennreal_balanced_product (F G : ℝ≥0∞) {a p : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ p) :
    (F ^ a * G ^ (p - a)) ^ (1 / 2 : ℝ) *
      (G ^ a * F ^ (p - a)) ^ (1 / 2 : ℝ) =
      F ^ (p / 2) * G ^ (p / 2) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  have hF : F ^ (a * (1 / 2 : ℝ)) * F ^ ((p - a) * (1 / 2 : ℝ)) = F ^ (p / 2) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    congr 1
    ring
  have hG : G ^ (a * (1 / 2 : ℝ)) * G ^ ((p - a) * (1 / 2 : ℝ)) = G ^ (p / 2) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ = (F ^ (a * (1 / 2 : ℝ)) * F ^ ((p - a) * (1 / 2 : ℝ))) *
      (G ^ (a * (1 / 2 : ℝ)) * G ^ ((p - a) * (1 / 2 : ℝ))) := by ring
    _ = _ := by rw [hF, hG]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyzBareBilinear_balanced_le (f g : SchwartzMap E ℂ) {a p : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ p) :
    glyzBareBilinear f g (p / 2) (p / 2) ≤
      glyzBareBilinear f g a (p - a) ^ (1 / 2 : ℝ) *
        glyzBareBilinear g f a (p - a) ^ (1 / 2 : ℝ) := by
  have h := glyz_lintegral_logconvex volume
    (((f.continuous.measurable.enorm.pow_const a).mul
      (g.continuous.measurable.enorm.pow_const (p - a))).aemeasurable)
    (((g.continuous.measurable.enorm.pow_const a).mul
      (f.continuous.measurable.enorm.pow_const (p - a))).aemeasurable)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  have he : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simpa only [he, glyz_ennreal_balanced_product _ _ ha hap, glyzBareBilinear] using h

theorem exists_glyz_symmetric_reverse_comparison {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) {a : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ (p : ℝ) - a) :
    ∃ K : ℝ, 0 < K ∧ ∀ N n q q' : ℕ, n + q ≤ N → n + q' ≤ N →
      ∀ i < 2 ^ n, ∀ j < 2 ^ n, GlyzDyadicSeparated n n i j →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      glyzBareBilinear (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ)
        (glyzDyadicBlock f N n j : SchwartzMap (GlyzSpace m) ℂ)
          ((p : ℝ) / 2) ((p : ℝ) / 2) ≤
        ENNReal.ofReal K * (2 ^ q : ℝ≥0∞) ^ a * (2 ^ q' : ℝ≥0∞) ^ ((p : ℝ) - a) *
          ENNReal.ofReal (glyzAsymmetricIntegralConstant m A N (n + q) (n + q') p a) *
          ENNReal.ofReal (glyzDyadicBilinearEnergy m N n n p ((p : ℝ) / 2) f i j) := by
  obtain ⟨K, hK, h⟩ := exists_glyz_asymmetric_reverse_comparison hA p ha hb
  refine ⟨K, hK, fun N n q q' hq hq' i hi j hj hs f hf => ?_⟩
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hb0 : 0 ≤ (p : ℝ) - a := zero_le_one.trans hb
  have hap : a ≤ (p : ℝ) := sub_nonneg.mp hb0
  let H := ENNReal.ofReal K * (2 ^ q : ℝ≥0∞) ^ a * (2 ^ q' : ℝ≥0∞) ^ ((p : ℝ) - a) *
    ENNReal.ofReal (glyzAsymmetricIntegralConstant m A N (n + q) (n + q') p a)
  let E₁ := glyzDyadicBilinearEnergy m N n n p a f i j
  let E₂ := glyzDyadicBilinearEnergy m N n n p a f j i
  have h₁ := ENNReal.rpow_le_rpow (h N n q q' hq hq' i hi j hj hs f hf)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have h₂ := ENNReal.rpow_le_rpow
    (h N n q q' hq hq' j hj i hi (glyzDyadicSeparated_symm hs) f hf)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  apply ((glyzBareBilinear_balanced_le (glyzDyadicBlock f N n i)
    (glyzDyadicBlock f N n j) ha0 hap).trans (mul_le_mul' h₁ h₂)).trans_eq
  change (H * ENNReal.ofReal E₁) ^ (1 / 2 : ℝ) *
    (H * ENNReal.ofReal E₂) ^ (1 / 2 : ℝ) = _
  rw [ENNReal.mul_rpow_of_nonneg H (ENNReal.ofReal E₁) (by norm_num),
    ENNReal.mul_rpow_of_nonneg H (ENNReal.ofReal E₂) (by norm_num)]
  have hH : H ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) = H := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hE₁ : 0 ≤ E₁ := glyzDyadicBilinearEnergy_nonneg m N n n p a f i j
  have hE₂ : 0 ≤ E₂ := glyzDyadicBilinearEnergy_nonneg m N n n p a f j i
  have henergy : ENNReal.ofReal E₁ ^ (1 / 2 : ℝ) * ENNReal.ofReal E₂ ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (glyzDyadicBilinearEnergy m N n n p ((p : ℝ) / 2) f i j) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hE₁ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg hE₂ (by norm_num),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hE₁ _)]
    congr 1
    have ht := glyzDyadicBilinearEnergy_logaffine m N n n p f i j
      (a₀ := (p : ℝ) - a) (a₁ := a) (θ := 1 / 2)
      hb0 ha0 (sub_le_self _ ha0) hap (by norm_num) (by norm_num)
    have haff : (1 / 2 : ℝ) * a + (1 - 1 / 2) * ((p : ℝ) - a) = (p : ℝ) / 2 := by ring
    rw [haff, glyzDyadicBilinearEnergy_symm m N n n p a f j i] at ht
    norm_num only at ht
    exact ht
  calc
    _ = (H ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ)) *
      (ENNReal.ofReal E₁ ^ (1 / 2 : ℝ) * ENNReal.ofReal E₂ ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [hH, henergy]

end PlanarNikodym
