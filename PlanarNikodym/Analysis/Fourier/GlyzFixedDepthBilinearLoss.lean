import PlanarNikodym.Analysis.Fourier.GlyzReverseLpComparison

/-! Actual fixed-depth separated bilinear bounds obtained from the
admissible asymmetric losses. Ceilings and the finitely many initial
scales are absorbed into one constant before the family is chosen. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace PlanarNikodym

theorem glyz_dyadic_bilinear_lp_le_trivial (m N n : ℕ)
    (p : ℝ≥0) (hp : 1 ≤ p) (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (i j : ℕ) :
    glyzBilinearLp p (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n j) ≤
      (2 : ℝ) ^ N *
        (glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i ^ (1 / 2 : ℝ) *
          glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n j ^ (1 / 2 : ℝ)) := by
  let W (k : ℕ) := glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n k
  have hW (k : ℕ) : 0 ≤ W k := glyz_dyadic_square_block_nonneg m N n k p f
  have hnorm (k : ℕ) : lpNorm (glyzDyadicBlock f N n k : SchwartzMap (GlyzSpace m) ℂ)
      p volume ≤ Real.sqrt ((2 : ℝ) ^ N * W k) :=
    (Real.le_sqrt lpNorm_nonneg (mul_nonneg (by positivity) (hW k))).mpr
      (glyz_schwartz_block_square_le_trivial m N n k p hp f)
  calc
    _ ≤ lpNorm (glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace m) ℂ) p volume *
        lpNorm (glyzDyadicBlock f N n j : SchwartzMap (GlyzSpace m) ℂ) p volume :=
      glyzBilinearLp_le p (zero_lt_one.trans_le hp) _ _
    _ ≤ Real.sqrt ((2 : ℝ) ^ N * W i) * Real.sqrt ((2 : ℝ) ^ N * W j) :=
      mul_le_mul (hnorm i) (hnorm j) lpNorm_nonneg (Real.sqrt_nonneg _)
    _ = (2 : ℝ) ^ N * (Real.sqrt (W i) * Real.sqrt (W j)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      calc
        _ = (Real.sqrt ((2 : ℝ) ^ N) * Real.sqrt ((2 : ℝ) ^ N)) *
          (Real.sqrt (W i) * Real.sqrt (W j)) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (by positivity)]
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

theorem glyzDyadicDepth_eventually_ge (n : ℕ) {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      n ≤ glyzDyadicDepth N alpha ∧ n ≤ glyzDyadicDepth N beta := by
  refine ⟨max ⌈(n : ℝ) / alpha⌉₊ ⌈(n : ℝ) / beta⌉₊, fun N hN => ?_⟩
  have hα : (n : ℝ) / alpha ≤ N :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_left _ _).trans hN))
  have hβ : (n : ℝ) / beta ≤ N :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  constructor
  · have hn : (n : ℝ) ≤ alpha * N := by
      have := (div_le_iff₀ ha).mp hα
      nlinarith
    exact_mod_cast hn.trans (Nat.le_ceil (alpha * N))
  · have hn : (n : ℝ) ≤ beta * N := by
      have := (div_le_iff₀ hb).mp hβ
      nlinarith
    exact_mod_cast hn.trans (Nat.le_ceil (beta * N))

theorem glyz_dyadic_refinement_power_le {N n : ℕ} {alpha a : ℝ}
    (hα : 0 ≤ alpha) (ha : 0 ≤ a) :
    (2 ^ (glyzDyadicDepth N alpha - n) : ℝ) ^ a ≤
      (2 : ℝ) ^ (a * alpha * N + a) := by
  have hdepth : (glyzDyadicDepth N alpha : ℝ) ≤ alpha * N + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hα (Nat.cast_nonneg N))).le
  have hq : ((glyzDyadicDepth N alpha - n : ℕ) : ℝ) ≤ alpha * N + 1 :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hdepth
  rw [← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

/-- An actual admissible asymmetric loss gives a uniform bilinear
bound at every scale for any fixed separated parent depth. -/
theorem glyz_fixed_depth_bilinear_of_admissible_asymmetric_loss
    {m A : ℕ} (hA : m < A) (p : ℝ≥0) {a : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ (p : ℝ) - a)
    {alpha beta e : ℝ} (hα : 0 < alpha) (hβ : 0 < beta)
    (hα1 : alpha ≤ 1) (hβ1 : beta ≤ 1)
    (he : GlyzAdmissibleAsymmetricLoss m A p a alpha beta e) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ i < 2 ^ n, ∀ j < 2 ^ n,
      GlyzDyadicSeparated n n i j →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      glyzBilinearLp p (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n j) ≤
        C * (2 : ℝ) ^ (((2 / (p : ℝ)) * (a * alpha + ((p : ℝ) - a) * beta + e)) * N) *
          (glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i ^ (1 / 2 : ℝ) *
            glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n j ^ (1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hrev⟩ := exists_glyz_reverse_lp_comparison hA p ha hb
  obtain ⟨he0, C₀, hC₀, hconst⟩ := he
  obtain ⟨N₀, hN₀⟩ := glyzDyadicDepth_eventually_ge n hα hβ
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hb0 : 0 ≤ (p : ℝ) - a := zero_le_one.trans hb
  have hp : 0 < (p : ℝ) := by linarith
  have hp₁ : 1 ≤ p := by
    show (1 : ℝ) ≤ p
    linarith
  let s : ℝ := a * alpha + ((p : ℝ) - a) * beta + e
  let r : ℝ := 2 / (p : ℝ)
  let C₁ : ℝ := K * C₀ * (2 : ℝ) ^ (p : ℝ)
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  let C : ℝ := max (C₁ ^ r) ((2 : ℝ) ^ N₀)
  have hC : 0 < C := lt_of_lt_of_le (Real.rpow_pos_of_pos hC₁ r) (le_max_left _ _)
  refine ⟨C, hC, fun N i hi j hj hsep f hf => ?_⟩
  let W : ℝ :=
    glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i ^ (1 / 2 : ℝ) *
      glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n j ^ (1 / 2 : ℝ)
  have hW : 0 ≤ W := mul_nonneg
    (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N n i p f) _)
    (Real.rpow_nonneg (glyz_dyadic_square_block_nonneg m N n j p f) _)
  change glyzBilinearLp p _ _ ≤ C * (2 : ℝ) ^ ((r * s) * N) * W
  by_cases hN : N₀ ≤ N
  · obtain ⟨hnα, hnβ⟩ := hN₀ N hN
    let q := glyzDyadicDepth N alpha - n
    let q' := glyzDyadicDepth N beta - n
    have hq : n + q = glyzDyadicDepth N alpha := Nat.add_sub_of_le hnα
    have hq' : n + q' = glyzDyadicDepth N beta := Nat.add_sub_of_le hnβ
    have hnorm := hrev N n q q'
      (hq ▸ glyzDyadicDepth_le hα1) (hq' ▸ glyzDyadicDepth_le hβ1) i hi j hj hsep f hf
    rw [hq, hq'] at hnorm
    let B := glyzAsymmetricIntegralConstant m A N
      (glyzDyadicDepth N alpha) (glyzDyadicDepth N beta) p a
    have hB : 0 ≤ B := glyzAsymmetricIntegralConstant_nonneg hA N _ _ p hp₁ ha0
      (sub_nonneg.mp hb0)
    have hcoef : K * (2 ^ q : ℝ) ^ a * (2 ^ q' : ℝ) ^ ((p : ℝ) - a) * B ≤
        C₁ * (2 : ℝ) ^ (s * N) := by
      have hαpow := glyz_dyadic_refinement_power_le (N := N) (n := n) hα.le ha0
      have hβpow := glyz_dyadic_refinement_power_le (N := N) (n := n) hβ.le hb0
      have hfirst : K * (2 ^ q : ℝ) ^ a * (2 ^ q' : ℝ) ^ ((p : ℝ) - a) ≤
          K * (2 : ℝ) ^ (a * alpha * N + a) *
            (2 : ℝ) ^ (((p : ℝ) - a) * beta * N + ((p : ℝ) - a)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hαpow hK.le) hβpow
          (by positivity) (by positivity)
      apply (mul_le_mul hfirst (hconst N) hB (by positivity)).trans_eq
      have hexp : (a * alpha * N + a) +
          (((p : ℝ) - a) * beta * N + ((p : ℝ) - a)) + e * N =
          (p : ℝ) + s * N := by dsimp only [s]; ring
      calc
        _ = K * C₀ * ((2 : ℝ) ^ (a * alpha * N + a) *
          (2 : ℝ) ^ (((p : ℝ) - a) * beta * N + ((p : ℝ) - a)) *
          (2 : ℝ) ^ (e * N)) := by ring
        _ = K * C₀ * (2 : ℝ) ^ ((p : ℝ) + s * N) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hexp]
        _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; dsimp only [C₁]; ring
    have hpow := Real.rpow_le_rpow (by positivity :
      0 ≤ K * (2 ^ q : ℝ) ^ a * (2 ^ q' : ℝ) ^ ((p : ℝ) - a) * B) hcoef hr
    have heq : (C₁ * (2 : ℝ) ^ (s * N)) ^ r =
        C₁ ^ r * (2 : ℝ) ^ ((r * s) * N) := by
      rw [Real.mul_rpow hC₁.le (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring
    rw [heq] at hpow
    exact hnorm.trans ((mul_le_mul_of_nonneg_right hpow hW).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hW))
  · have hpower : (2 : ℝ) ^ N ≤ C * (2 : ℝ) ^ ((r * s) * N) := by
      calc
        _ ≤ (2 : ℝ) ^ N₀ := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt (Nat.lt_of_not_ge hN))
        _ ≤ C := le_max_right _ _
        _ ≤ C * (2 : ℝ) ^ ((r * s) * N) := by
          have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((r * s) * N) :=
            Real.one_le_rpow (by norm_num) (by positivity)
          nlinarith
    exact (glyz_dyadic_bilinear_lp_le_trivial m N n p hp₁ f i j).trans
      (mul_le_mul_of_nonneg_right hpower hW)

/-- Every positive perturbation of the actual optimal asymmetric
loss supplies the preceding family-uniform norm estimate. No
attainment of the optimal exponent is asserted. -/
theorem glyz_fixed_depth_bilinear_of_optimal_asymmetric_loss
    {m A : ℕ} (hA : m < A) (p : ℝ≥0) {a : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ (p : ℝ) - a)
    {alpha beta : ℝ} (hα : 0 < alpha) (hβ : 0 < beta)
    (hα1 : alpha ≤ 1) (hβ1 : beta ≤ 1) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ i < 2 ^ n, ∀ j < 2 ^ n,
      GlyzDyadicSeparated n n i j →
      ∀ f : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m N f →
      glyzBilinearLp p (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n j) ≤
        C * (2 : ℝ) ^ (((2 / (p : ℝ)) *
          (a * alpha + ((p : ℝ) - a) * beta +
            (glyzOptimalAsymmetricLoss m A p a alpha beta + ε))) * N) *
          (glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n i ^ (1 / 2 : ℝ) *
            glyzDyadicBlock (fun k => lpNorm (f k) p volume ^ (2 : ℕ)) N n j ^ (1 / 2 : ℝ)) := by
  have hp : 1 ≤ p := by
    show (1 : ℝ) ≤ p
    linarith
  have he := glyz_admissible_asymmetric_loss_of_optimal_lt hA p hp
    (zero_le_one.trans ha) (show a ≤ (p : ℝ) by linarith) alpha beta
    (lt_add_of_pos_right _ hε)
  exact glyz_fixed_depth_bilinear_of_admissible_asymmetric_loss
    hA p ha hb hα hβ hα1 hβ1 he n

end PlanarNikodym
