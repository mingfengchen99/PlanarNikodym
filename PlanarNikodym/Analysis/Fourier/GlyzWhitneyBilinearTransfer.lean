import PlanarNikodym.Analysis.Fourier.GlyzWhitneyAffineFamily

/-! Actual affine transport from depth-two separated pairs to the
Whitney pairs at every generation. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace PlanarNikodym

theorem glyz_rpow_half_mul_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) ≤ x + y := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

theorem glyzDyadicSeparated_two_zero {k : ℕ} (hk : 2 ≤ k) :
    GlyzDyadicSeparated 2 2 0 k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold GlyzDyadicSeparated glyzDyadicCenter glyzDyadicScale
  norm_num
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem glyz_whitney_bilinear_affine_transfer (m d r i k : ℕ)
    (hk : i + k < 2 ^ d) (p : ℝ≥0) (hp : 0 < p)
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (hf : GlyzDyadicSupported m (d + r) f)
    (C : ℝ)
    (hC : ∀ g : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m (r + 2) g →
      glyzBilinearLp p (glyzDyadicBlock g (r + 2) 2 0) (glyzDyadicBlock g (r + 2) 2 k) ≤
        C * (glyzDyadicBlock (fun h => lpNorm (g h) p volume ^ (2 : ℕ)) (r + 2) 2 0 +
          glyzDyadicBlock (fun h => lpNorm (g h) p volume ^ (2 : ℕ)) (r + 2) 2 k)) :
    glyzBilinearLp p (glyzDyadicBlock f (d + r) d i) (glyzDyadicBlock f (d + r) d (i + k)) ≤
      C * (glyzDyadicBlock (fun h => lpNorm (f h) p volume ^ (2 : ℕ)) (d + r) d i +
        glyzDyadicBlock (fun h => lpNorm (f h) p volume ^ (2 : ℕ)) (d + r) d (i + k)) := by
  have hi : i + 0 < 2 ^ d := by omega
  have h := hC (glyzWhitneyFamily m d r i f) (glyzWhitneyFamily_supported m d r i f hf)
  rw [glyzWhitneyFamily_block m d r i 0 hi, glyzWhitneyFamily_block m d r i k hk,
    glyzWhitneyFamily_energy m d r i 0 hi, glyzWhitneyFamily_energy m d r i k hk] at h
  simp only [Nat.add_zero, glyzWhitneyPullback, glyzBilinearLp_frequencyAffine _ _ p hp] at h
  apply (mul_le_mul_iff_right₀
    (sq_pos_of_pos (glyzAffineLpFactor_pos (glyzWhitneyAffine m d i) p))).mp
  nlinarith [h]

theorem glyz_whitney_pair_gap {i j : ℕ} (hij : i ≤ j)
    (h : 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1) :
    2 ≤ j - i ∧ j - i < 4 := by
  have hd : i / 2 ≤ j / 2 := Nat.div_le_div_right hij
  rw [Nat.dist_eq_sub_of_le hij, Nat.dist_eq_sub_of_le hd] at h
  omega

/-- A bound for actual depth-two families gives the corresponding
bound at every Whitney layer, with relative depth `N-d+2`. -/
theorem glyz_whitney_pair_of_fixed_depth (m N d : ℕ) (hd : d ≤ N)
    (p : ℝ≥0) (hp : 0 < p) {C s : ℝ} (hC : 0 ≤ C)
    (hfixed : ∀ M : ℕ, ∀ i < 2 ^ 2, ∀ j < 2 ^ 2, GlyzDyadicSeparated 2 2 i j →
      ∀ g : ℕ → SchwartzMap (GlyzSpace m) ℂ, GlyzDyadicSupported m M g →
      glyzBilinearLp p (glyzDyadicBlock g M 2 i) (glyzDyadicBlock g M 2 j) ≤
        C * (2 : ℝ) ^ (s * M) *
          (glyzDyadicBlock (fun h => lpNorm (g h) p volume ^ (2 : ℕ)) M 2 i ^ (1 / 2 : ℝ) *
            glyzDyadicBlock (fun h => lpNorm (g h) p volume ^ (2 : ℕ)) M 2 j ^ (1 / 2 : ℝ)))
    (f : ℕ → SchwartzMap (GlyzSpace m) ℂ) (hf : GlyzDyadicSupported m N f)
    {i j : ℕ} (hi : i < 2 ^ d) (hj : j < 2 ^ d)
    (hpair : 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1) :
    glyzBilinearLp p (glyzDyadicBlock f N d i) (glyzDyadicBlock f N d j) ≤
      C * (2 : ℝ) ^ (s * ((N - d + 2 : ℕ) : ℝ)) *
        (glyzDyadicBlock (fun h => lpNorm (f h) p volume ^ (2 : ℕ)) N d i +
          glyzDyadicBlock (fun h => lpNorm (f h) p volume ^ (2 : ℕ)) N d j) := by
  have hordered (i j : ℕ) (hij : i ≤ j) (hj : j < 2 ^ d)
      (hpair : 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1) :
      glyzBilinearLp p (glyzDyadicBlock f N d i) (glyzDyadicBlock f N d j) ≤
        C * (2 : ℝ) ^ (s * ((N - d + 2 : ℕ) : ℝ)) *
          (glyzDyadicBlock (fun h => lpNorm (f h) p volume ^ (2 : ℕ)) N d i +
            glyzDyadicBlock (fun h => lpNorm (f h) p volume ^ (2 : ℕ)) N d j) := by
    obtain ⟨hk₂, hk₄⟩ := glyz_whitney_pair_gap hij hpair
    have hij' : i + (j - i) = j := Nat.add_sub_of_le hij
    have hN : d + (N - d) = N := Nat.add_sub_of_le hd
    have ht := glyz_whitney_bilinear_affine_transfer m d (N - d) i (j - i)
      (by omega) p hp f (by simpa only [hN] using hf) (C * (2 : ℝ) ^ (s * ((N - d + 2 : ℕ) : ℝ)))
      (fun g hg => (hfixed (N - d + 2) 0 (by norm_num) (j - i)
        (by simpa using hk₄) (glyzDyadicSeparated_two_zero hk₂) g hg).trans
          (mul_le_mul_of_nonneg_left
            (glyz_rpow_half_mul_le_add
              (glyz_dyadic_square_block_nonneg m _ _ _ p g)
              (glyz_dyadic_square_block_nonneg m _ _ _ p g)) (by positivity)))
    simpa only [hN, hij'] using ht
  by_cases hij : i ≤ j
  · exact hordered i j hij hj hpair
  · rw [glyzBilinearLp_symm p hp]
    simpa only [add_comm] using hordered j i (by omega) hi
      (by simpa only [Nat.dist_comm] using hpair)

end PlanarNikodym
