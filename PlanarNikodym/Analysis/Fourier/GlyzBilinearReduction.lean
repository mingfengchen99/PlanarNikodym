import PlanarNikodym.Analysis.Fourier.GlyzBilinearLp

/-! Finite Whitney bilinear-to-linear reduction for actual Schwartz sums.
The bilinear estimate is an explicit hypothesis; this module proves the
analytic reduction and does not assert the deeper dimension gain. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzPairSum (I : Finset ℕ) (H : ℕ → ℕ → Prop) [DecidableRel H]
    (f : ℕ → SchwartzMap E ℂ) : E → ℂ :=
  ∑ i ∈ I, ∑ j ∈ I, if H i j then (fun x => f i x * star (f j x)) else 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyzPairSum_apply (I : Finset ℕ) (H : ℕ → ℕ → Prop) [DecidableRel H]
    (f : ℕ → SchwartzMap E ℂ) (x : E) :
    glyzPairSum I H f x = ∑ i ∈ I, ∑ j ∈ I,
      if H i j then f i x * star (f j x) else 0 := by
  simp only [glyzPairSum, Finset.sum_apply, Pi.zero_apply, ite_apply]

theorem memLp_glyzPairSum (I : Finset ℕ) (H : ℕ → ℕ → Prop) [DecidableRel H]
    (f : ℕ → SchwartzMap E ℂ) (p : ℝ≥0) (hp : 0 < p) :
    MemLp (glyzPairSum I H f) (p / 2 : ℝ≥0) volume := by
  apply memLp_finsetSum'
  intro i _
  apply memLp_finsetSum'
  intro j _
  split_ifs
  · exact memLp_glyz_pair p hp (f i) (f j)
  · exact MemLp.zero

theorem lpNorm_glyzPairSum_le (I : Finset ℕ) (H : ℕ → ℕ → Prop) [DecidableRel H]
    (f : ℕ → SchwartzMap E ℂ) (p : ℝ≥0) (hp : 2 ≤ p) :
    lpNorm (glyzPairSum I H f) (p / 2 : ℝ≥0) volume ≤
      ∑ i ∈ I, ∑ j ∈ I, if H i j then glyzBilinearLp p (f i) (f j) else 0 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 2) hp
  have hq : (1 : ℝ≥0∞) ≤ ((p / 2 : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (show (1 : ℝ≥0) ≤ p / 2 by exact (le_div_iff₀ (by norm_num)).2 (by simpa using hp))
  have ht (i j : ℕ) : MemLp (if H i j then (fun x => f i x * star (f j x)) else 0)
      (p / 2 : ℝ≥0) volume := by
    split_ifs
    · exact memLp_glyz_pair p hp0 (f i) (f j)
    · exact MemLp.zero
  calc
    _ ≤ ∑ i ∈ I, lpNorm (∑ j ∈ I,
        if H i j then (fun x => f i x * star (f j x)) else 0) (p / 2 : ℝ≥0) volume :=
      lpNorm_sum_le (fun i _ => memLp_finsetSum' I (fun j _ => ht i j)) hq
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, lpNorm
        (if H i j then (fun x => f i x * star (f j x)) else 0) (p / 2 : ℝ≥0) volume :=
      Finset.sum_le_sum fun i _ => lpNorm_sum_le (fun j _ => ht i j) hq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp [glyzBilinearLp]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyzDyadicBlock_apply (f : ℕ → SchwartzMap E ℂ) (N n i : ℕ) (x : E) :
    glyzDyadicBlock f N n i x = glyzDyadicBlock (fun j => f j x) N n i := by
  simp [glyzDyadicBlock]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyz_whitney_schwartz_identity (f : ℕ → SchwartzMap E ℂ) (N : ℕ) :
    (fun x => (∑ i ∈ Finset.range (2 ^ N), f i x) *
      star (∑ i ∈ Finset.range (2 ^ N), f i x)) =
      glyzPairSum (Finset.range (2 ^ N)) (fun i j => Nat.dist i j ≤ 1) f +
        ∑ n ∈ Finset.range N, glyzPairSum (Finset.range (2 ^ (n + 1)))
          (fun i j => 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1)
          (glyzDyadicBlock f N (n + 1)) := by
  ext x
  simpa only [Pi.add_apply, Finset.sum_apply, glyzPairSum_apply,
    glyzDyadicBlock_apply, glyzNearEnergy, glyzWhitneyEnergy] using
      glyz_dyadic_whitney_identity (fun i => f i x) N

theorem glyz_whitney_lp_reduction (f : ℕ → SchwartzMap E ℂ) (N : ℕ)
    (p : ℝ≥0) (hp : 2 ≤ p) :
    lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) p volume ^ (2 : ℕ) ≤
      (∑ i ∈ Finset.range (2 ^ N), ∑ j ∈ Finset.range (2 ^ N),
        if Nat.dist i j ≤ 1 then glyzBilinearLp p (f i) (f j) else 0) +
      ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (2 ^ (n + 1)),
        ∑ j ∈ Finset.range (2 ^ (n + 1)),
          if 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1
          then glyzBilinearLp p (glyzDyadicBlock f N (n + 1) i)
            (glyzDyadicBlock f N (n + 1) j) else 0 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 2) hp
  have hq : (1 : ℝ≥0∞) ≤ ((p / 2 : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast (show (1 : ℝ≥0) ≤ p / 2 by exact (le_div_iff₀ (by norm_num)).2 (by simpa using hp))
  have hs : (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x) =
      ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap E ℂ) : E → ℂ) := by
    ext x
    simp
  rw [hs, ← glyzBilinearLp_self p hp0 (∑ i ∈ Finset.range (2 ^ N), f i)]
  change lpNorm (fun x => (∑ i ∈ Finset.range (2 ^ N), f i) x *
    star ((∑ i ∈ Finset.range (2 ^ N), f i) x)) (p / 2 : ℝ≥0) volume ≤ _
  simp only [sum_apply]
  rw [glyz_whitney_schwartz_identity]
  apply (lpNorm_add_le (memLp_glyzPairSum _ _ f p hp0) hq).trans
  apply add_le_add (lpNorm_glyzPairSum_le _ _ f p hp)
  exact (lpNorm_sum_le (fun n _ => memLp_glyzPairSum _ _ _ p hp0) hq).trans
    (Finset.sum_le_sum fun n _ => lpNorm_glyzPairSum_le _ _ _ p hp)

end PlanarNikodym
