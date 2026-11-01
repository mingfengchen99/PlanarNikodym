import PlanarNikodym.Analysis.Fourier.GlyzBilinearReduction

/-! The quantitative finite bilinear-to-linear theorem. Every block on
both sides is a sum of the original pieces, not an independently chosen
family. The scale coefficients remain explicit bilinear hypotheses. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_near_bilinear_sum_le (I : Finset ℕ) (f : ℕ → SchwartzMap E ℂ)
    (p : ℝ≥0) (hp : 0 < p) :
    (∑ i ∈ I, ∑ j ∈ I, if Nat.dist i j ≤ 1 then glyzBilinearLp p (f i) (f j) else 0) ≤
      6 * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ (2 : ℕ) := by
  apply le_trans _ (glyz_near_weighted_sum_le I
    (fun i => lpNorm (f i : E → ℂ) p volume ^ (2 : ℕ)) (fun _ _ => sq_nonneg _))
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact glyzBilinearLp_le_sq_add_sq p hp (f i) (f j)
  · exact le_rfl

/-- The finite form of the analytic Whitney reduction in Lemma 2.2.
An actual bilinear bound at every separated sibling scale gives an
actual linear bound, with the scale sum and multiplicities exposed. -/
theorem glyz_bilinear_to_linear (f : ℕ → SchwartzMap E ℂ) (N : ℕ)
    (p : ℝ≥0) (hp : 2 ≤ p) (C : ℕ → ℝ) (hC : ∀ n < N, 0 ≤ C n)
    (hbil : ∀ n < N, ∀ i < 2 ^ (n + 1), ∀ j < 2 ^ (n + 1),
      2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1 →
      glyzBilinearLp p (glyzDyadicBlock f N (n + 1) i) (glyzDyadicBlock f N (n + 1) j) ≤
        C n * (glyzDyadicBlock (fun k => lpNorm (f k : E → ℂ) p volume ^ (2 : ℕ)) N (n + 1) i +
          glyzDyadicBlock (fun k => lpNorm (f k : E → ℂ) p volume ^ (2 : ℕ)) N (n + 1) j)) :
    lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
      (6 + 8 * ∑ n ∈ Finset.range N, C n) *
        ∑ k ∈ Finset.range (2 ^ N), lpNorm (f k : E → ℂ) p volume ^ (2 : ℕ) := by
  let W : ℕ → ℝ := fun k => lpNorm (f k : E → ℂ) p volume ^ (2 : ℕ)
  have hW (k : ℕ) : 0 ≤ W k := sq_nonneg _
  have hS (n i : ℕ) : 0 ≤ glyzDyadicBlock W N n i :=
    Finset.sum_nonneg fun j _ => hW _
  have hlayer (n : ℕ) (hn : n < N) :
      (∑ i ∈ Finset.range (2 ^ (n + 1)), ∑ j ∈ Finset.range (2 ^ (n + 1)),
        if 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1
        then glyzBilinearLp p (glyzDyadicBlock f N (n + 1) i)
          (glyzDyadicBlock f N (n + 1) j) else 0) ≤
        (8 * C n) * ∑ k ∈ Finset.range (2 ^ N), W k := by
    calc
      _ ≤ ∑ i ∈ Finset.range (2 ^ (n + 1)), ∑ j ∈ Finset.range (2 ^ (n + 1)),
          if 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1 then
            C n * (glyzDyadicBlock W N (n + 1) i + glyzDyadicBlock W N (n + 1) j) else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        split_ifs with hij
        · exact hbil n hn i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
        · exact le_rfl
      _ = C n * ∑ i ∈ Finset.range (2 ^ (n + 1)), ∑ j ∈ Finset.range (2 ^ (n + 1)),
          if 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1 then
            glyzDyadicBlock W N (n + 1) i + glyzDyadicBlock W N (n + 1) j else 0 := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
      _ ≤ C n * (8 * ∑ i ∈ Finset.range (2 ^ (n + 1)), glyzDyadicBlock W N (n + 1) i) :=
        mul_le_mul_of_nonneg_left (glyz_whitney_weighted_sum_le _ _ (fun i _ => hS _ i)) (hC n hn)
      _ = _ := by rw [glyz_sum_dyadic_blocks W N (n + 1) (by omega)]; ring
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 2) hp
  apply (glyz_whitney_lp_reduction f N p hp).trans
  calc
    _ ≤ 6 * (∑ k ∈ Finset.range (2 ^ N), W k) +
        ∑ n ∈ Finset.range N, (8 * C n) * ∑ k ∈ Finset.range (2 ^ N), W k :=
      add_le_add (glyz_near_bilinear_sum_le _ f p hp0)
        (Finset.sum_le_sum fun n hn => hlayer n (Finset.mem_range.mp hn))
    _ = _ := by simp only [← Finset.sum_mul, ← Finset.mul_sum]; ring

end PlanarNikodym
