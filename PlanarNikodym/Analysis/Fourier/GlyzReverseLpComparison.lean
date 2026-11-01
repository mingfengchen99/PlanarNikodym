import PlanarNikodym.Analysis.Fourier.GlyzSymmetricReverseComparison

/-! Conversion of the integral comparison in GLYZ Lemma 3.4 to the
actual bilinear Lp norm used by the Whitney reduction. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyzBilinearLp_pow_eq_bare (p : ℝ≥0) (hp : 0 < p)
    (f g : SchwartzMap E ℂ) :
    ENNReal.ofReal (glyzBilinearLp p f g) ^ ((p : ℝ) / 2) =
      glyzBareBilinear f g ((p : ℝ) / 2) ((p : ℝ) / 2) := by
  have hp₂ : (p / 2 : ℝ≥0) ≠ 0 := div_ne_zero hp.ne' (by norm_num)
  unfold glyzBilinearLp glyzBareBilinear
  rw [ofReal_lpNorm (memLp_glyz_pair p hp f g)]
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := fun x => f x * star (g x)) (μ := volume) hp₂
  simp only [NNReal.coe_div, NNReal.coe_ofNat] at h
  rw [h]
  apply lintegral_congr
  intro x
  have hstar : ‖star (g x)‖ₑ = ‖g x‖ₑ := by simp [enorm_eq_nnnorm]
  rw [enorm_mul, hstar, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

theorem glyzBilinearLp_le_of_bare_le (p : ℝ≥0) (hp : 0 < p)
    (f g : SchwartzMap E ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : glyzBareBilinear f g ((p : ℝ) / 2) ((p : ℝ) / 2) ≤ ENNReal.ofReal C) :
    glyzBilinearLp p f g ≤ C ^ (2 / (p : ℝ)) := by
  have hpR : 0 < (p : ℝ) := hp
  have he : 0 ≤ 2 / (p : ℝ) := by positivity
  have hpow := ENNReal.rpow_le_rpow h he
  rw [← glyzBilinearLp_pow_eq_bare p hp f g, ← ENNReal.rpow_mul] at hpow
  have hm : ((p : ℝ) / 2) * (2 / (p : ℝ)) = 1 := by field_simp
  rw [hm, ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg hC he] at hpow
  exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hC _)).mp hpow

theorem glyzDyadicBilinearEnergy_balanced_rpow (m N n n' : ℕ)
    (p : ℝ≥0) (hp : 0 < p) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) :
    glyzDyadicBilinearEnergy m N n n' p ((p : ℝ) / 2) f i j ^ (2 / (p : ℝ)) =
      glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i ^ (1 / 2 : ℝ) *
        glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n' j ^ (1 / 2 : ℝ) := by
  have hpR : (p : ℝ) ≠ 0 := ne_of_gt hp
  have h₁ : ((p : ℝ) / 2 / 2) * (2 / (p : ℝ)) = 1 / 2 := by field_simp
  have h₂ : (((p : ℝ) - (p : ℝ) / 2) / 2) * (2 / (p : ℝ)) = 1 / 2 := by
    field_simp
    ring
  unfold glyzDyadicBilinearEnergy
  rw [Real.mul_rpow
    (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N n i p f) _)
    (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N n' j p f) _),
    ← Real.rpow_mul (glyz_dyadic_square_block_nonneg m N n i p f),
    ← Real.rpow_mul (glyz_dyadic_square_block_nonneg m N n' j p f), h₁, h₂]

/-- The actual bilinear norm bound furnished by Lemma 3.4, in the
normalization used in the finite Whitney reduction. -/
theorem exists_glyz_reverse_lp_comparison {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) {a : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ (p : ℝ) - a) :
    ∃ K : ℝ, 0 < K ∧ ∀ N n q q' : ℕ, n + q ≤ N → n + q' ≤ N →
      ∀ i < 2 ^ n, ∀ j < 2 ^ n, GlyzDyadicSeparated n n i j →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      glyzBilinearLp p (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n j) ≤
        (K * (2 ^ q : ℝ) ^ a * (2 ^ q' : ℝ) ^ ((p : ℝ) - a) *
          glyzAsymmetricIntegralConstant m A N (n + q) (n + q') p a) ^ (2 / (p : ℝ)) *
        (glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i ^ (1 / 2 : ℝ) *
          glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n j ^ (1 / 2 : ℝ)) := by
  obtain ⟨K, hK, h⟩ := exists_glyz_symmetric_reverse_comparison hA p ha hb
  refine ⟨K, hK, fun N n q q' hq hq' i hi j hj hs f hf => ?_⟩
  have hp : 0 < p := by
    have : (0 : ℝ) < p := by linarith
    exact this
  have hp₁ : 1 ≤ p := by
    have : (1 : ℝ) ≤ p := by linarith
    exact this
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hb0 : 0 ≤ (p : ℝ) - a := zero_le_one.trans hb
  let B := glyzAsymmetricIntegralConstant m A N (n + q) (n + q') p a
  let C := K * (2 ^ q : ℝ) ^ a * (2 ^ q' : ℝ) ^ ((p : ℝ) - a) * B
  let W := glyzDyadicBilinearEnergy m N n n p ((p : ℝ) / 2) f i j
  have hB : 0 ≤ B := glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp₁ ha0
    (sub_nonneg.mp hb0)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hW : 0 ≤ W := glyzDyadicBilinearEnergy_nonneg m N n n p _ f i j
  have he : ENNReal.ofReal (C * W) =
      ENNReal.ofReal K * (2 ^ q : ℝ≥0∞) ^ a * (2 ^ q' : ℝ≥0∞) ^ ((p : ℝ) - a) *
        ENNReal.ofReal B * ENNReal.ofReal W := by
    rw [ENNReal.ofReal_mul hC]
    dsimp only [C]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul hK.le,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ q) ha0,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ q') hb0]
    norm_num
  have hh : glyzBareBilinear (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ)
      (glyzDyadicBlock f N n j : SchwartzMap (GlyzSpace m) ℂ)
        ((p : ℝ) / 2) ((p : ℝ) / 2) ≤ ENNReal.ofReal (C * W) := by
    rw [he]
    exact h N n q q' hq hq' i hi j hj hs f hf
  have hnorm := glyzBilinearLp_le_of_bare_le p hp (glyzDyadicBlock f N n i)
    (glyzDyadicBlock f N n j) (mul_nonneg hC hW) hh
  rw [Real.mul_rpow hC hW] at hnorm
  simpa only [W, glyzDyadicBilinearEnergy_balanced_rpow m N n n p hp f i j, C, B] using hnorm

end PlanarNikodym
