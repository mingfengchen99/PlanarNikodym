import PlanarNikodym.Analysis.Fourier.GlyzDyadicRescaling

/-! Exact refinement of dyadic block sums and inherited interval
separation. No analytic estimate is involved in these identities. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

/-- Refining a dyadic parent by an arbitrary number of generations
recovers the actual parent sum, including every finest piece once. -/
theorem glyzDyadicBlock_refine {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (N n q i : ℕ) (hq : n + q ≤ N) :
    glyzDyadicBlock f N n i =
      ∑ j ∈ Finset.range (2 ^ q), glyzDyadicBlock f N (n + q) (i * 2 ^ q + j) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [ih (by omega), pow_succ, Nat.mul_comm (2 ^ q) 2, glyz_sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [glyzDyadicBlock_children f (show n + q < N by omega)]
    congr 1 <;> congr 1 <;> ring

/-- Composition of actual dyadic block operators. -/
theorem glyzDyadicBlock_comp {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (N n m i : ℕ) (hnm : n ≤ m) (hmN : m ≤ N) :
    glyzDyadicBlock (glyzDyadicBlock f N m) m n i = glyzDyadicBlock f N n i := by
  have h := glyzDyadicBlock_refine f N n (m - n) i (by omega)
  simpa only [Nat.add_sub_of_le hnm, glyzDyadicBlock] using h.symm

theorem glyzDyadicBlock_descendant_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (N n n₀ i u : ℕ) (h₀ : n₀ ≤ n) (hn : n ≤ N) (hu : u < 2 ^ (n - n₀)) :
    glyzDyadicBlock f N n (i * 2 ^ (n - n₀) + u) ≤ glyzDyadicBlock f N n₀ i := by
  rw [glyzDyadicBlock_refine f N n₀ (n - n₀) i (by omega),
    Nat.add_sub_of_le h₀]
  exact Finset.single_le_sum
    (fun v _ => (show 0 ≤ glyzDyadicBlock f N n (i * 2 ^ (n - n₀) + v) from
      Finset.sum_nonneg fun _ _ => hf _)) (Finset.mem_range.mpr hu)

theorem glyzDyadicCenter_descendant_dist {n q i j : ℕ} (hj : j < 2 ^ q) :
    |glyzDyadicCenter (n + q) (i * 2 ^ q + j) - glyzDyadicCenter n i| +
      glyzDyadicScale (n + q) / 2 ≤ glyzDyadicScale n / 2 := by
  have hq := glyzDyadicScale_pos q
  have hn := glyzDyadicScale_pos n
  have hj' : (j : ℝ) + 1 ≤ (2 : ℝ) ^ q := by exact_mod_cast hj
  have he : glyzDyadicScale q * (2 : ℝ) ^ q = 1 :=
    inv_mul_cancel₀ (by positivity)
  have hlow : glyzDyadicScale q / 2 ≤ glyzDyadicCenter q j := by
    unfold glyzDyadicCenter
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hhigh : glyzDyadicCenter q j ≤ 1 - glyzDyadicScale q / 2 := by
    unfold glyzDyadicCenter
    nlinarith
  rw [← glyzDyadicCenter_rescale, glyzDyadicScale_add]
  change |glyzDyadicScale n * (i : ℝ) + glyzDyadicScale n * glyzDyadicCenter q j -
    glyzDyadicScale n * ((i : ℝ) + 1 / 2)| + _ ≤ _
  rw [show glyzDyadicScale n * (i : ℝ) + glyzDyadicScale n * glyzDyadicCenter q j -
    glyzDyadicScale n * ((i : ℝ) + 1 / 2) =
      glyzDyadicScale n * (glyzDyadicCenter q j - 1 / 2) by ring,
    abs_mul, abs_of_pos hn]
  have hdist : |glyzDyadicCenter q j - 1 / 2| ≤ (1 - glyzDyadicScale q) / 2 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith [mul_le_mul_of_nonneg_left hdist hn.le]

end PlanarNikodym
