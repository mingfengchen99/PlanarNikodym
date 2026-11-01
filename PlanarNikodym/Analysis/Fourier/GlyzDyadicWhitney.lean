import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The finite dyadic Whitney identity behind GLYZ Lemma 2.2.
All block functions are actual finite sums of the finest pieces. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

theorem glyz_sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ Finset.range (2 * N), f i) =
      ∑ i ∈ Finset.range N, (f (2 * i) + f (2 * i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    exact add_assoc _ _ _

def glyzDyadicBlock {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N n i : ℕ) : M :=
  ∑ j ∈ Finset.range (2 ^ (N - n)), f (i * 2 ^ (N - n) + j)

theorem glyzDyadicBlock_zero {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    glyzDyadicBlock f N 0 0 = ∑ j ∈ Finset.range (2 ^ N), f j := by
  simp [glyzDyadicBlock]

theorem glyzDyadicBlock_finest {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N i : ℕ) :
    glyzDyadicBlock f N N i = f i := by simp [glyzDyadicBlock]

theorem glyzDyadicBlock_children {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {N n : ℕ} (hn : n < N) (i : ℕ) :
    glyzDyadicBlock f N n i =
      glyzDyadicBlock f N (n + 1) (2 * i) + glyzDyadicBlock f N (n + 1) (2 * i + 1) := by
  have he : N - n = (N - (n + 1)) + 1 := by omega
  unfold glyzDyadicBlock
  rw [he, pow_succ, mul_two, Finset.sum_range_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> congr 1 <;> ring

theorem glyz_sum_dyadic_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (N n : ℕ) (hn : n ≤ N) :
    (∑ i ∈ Finset.range (2 ^ n), glyzDyadicBlock f N n i) =
      ∑ j ∈ Finset.range (2 ^ N), f j := by
  induction n with
  | zero => simp [glyzDyadicBlock_zero]
  | succ n ih =>
    rw [pow_succ, Nat.mul_comm (2 ^ n) 2, glyz_sum_range_two_mul]
    simp_rw [← glyzDyadicBlock_children f (show n < N by omega)]
    exact ih (by omega)

def glyzNearEnergy (F : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if Nat.dist i j ≤ 1 then F i * star (F j) else 0

def glyzWhitneyEnergy (F : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
    if 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1 then F i * star (F j) else 0

theorem glyz_near_parent {i j : ℕ} (h : Nat.dist i j ≤ 1) :
    Nat.dist (i / 2) (j / 2) ≤ 1 := by unfold Nat.dist at *; omega

theorem glyz_whitney_pair_distance {i j : ℕ}
    (h : 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1) :
    Nat.dist i j = 2 ∨ Nat.dist i j = 3 := by unfold Nat.dist at *; omega

theorem glyz_energy_split (F : ℕ → ℂ) (M : ℕ) :
    glyzNearEnergy F (2 * M) + glyzWhitneyEnergy F (2 * M) =
      ∑ i ∈ Finset.range (2 * M), ∑ j ∈ Finset.range (2 * M),
        if Nat.dist (i / 2) (j / 2) ≤ 1 then F i * star (F j) else 0 := by
  unfold glyzNearEnergy glyzWhitneyEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hn : Nat.dist i j ≤ 1
  · have hp := glyz_near_parent hn
    have hf : ¬ 2 ≤ Nat.dist i j := by omega
    simp [hn, hp, hf]
  · have hf : 2 ≤ Nat.dist i j := by omega
    simp [hn, hf]

theorem glyz_energy_coarsen (F : ℕ → ℂ) (M : ℕ) :
    glyzNearEnergy (fun i => F (2 * i) + F (2 * i + 1)) M =
      glyzNearEnergy F (2 * M) + glyzWhitneyEnergy F (2 * M) := by
  rw [glyz_energy_split, glyz_sum_range_two_mul]
  unfold glyzNearEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [glyz_sum_range_two_mul (fun j => if Nat.dist (2 * i / 2) (j / 2) ≤ 1 then
    F (2 * i) * star (F j) else 0) M,
    glyz_sum_range_two_mul (fun j => if Nat.dist ((2 * i + 1) / 2) (j / 2) ≤ 1 then
      F (2 * i + 1) * star (F j) else 0) M]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hi₀ : 2 * i / 2 = i := by omega
  have hi₁ : (2 * i + 1) / 2 = i := by omega
  have hj₀ : 2 * j / 2 = j := by omega
  have hj₁ : (2 * j + 1) / 2 = j := by omega
  rw [hi₀, hi₁, hj₀, hj₁]
  by_cases h : Nat.dist i j ≤ 1 <;> simp [h, star_add, add_mul, mul_add]
  all_goals ring

theorem glyz_dyadic_energy_coarsen (f : ℕ → ℂ) {N n : ℕ} (hn : n < N) :
    glyzNearEnergy (glyzDyadicBlock f N n) (2 ^ n) =
      glyzNearEnergy (glyzDyadicBlock f N (n + 1)) (2 ^ (n + 1)) +
        glyzWhitneyEnergy (glyzDyadicBlock f N (n + 1)) (2 ^ (n + 1)) := by
  have he : glyzDyadicBlock f N n = fun i =>
      glyzDyadicBlock f N (n + 1) (2 * i) + glyzDyadicBlock f N (n + 1) (2 * i + 1) :=
    funext (glyzDyadicBlock_children f hn)
  rw [he, glyz_energy_coarsen, pow_succ, Nat.mul_comm (2 ^ n) 2]

theorem glyz_dyadic_energy_telescope (f : ℕ → ℂ) (N k : ℕ) (hk : k ≤ N) :
    glyzNearEnergy (glyzDyadicBlock f N 0) 1 =
      glyzNearEnergy (glyzDyadicBlock f N k) (2 ^ k) +
        ∑ n ∈ Finset.range k, glyzWhitneyEnergy (glyzDyadicBlock f N (n + 1)) (2 ^ (n + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), glyz_dyadic_energy_coarsen f (show k < N by omega), Finset.sum_range_succ]
    ring

/-- Exact finite Whitney expansion of the square of the actual sum.
The first Whitney layer is empty; it is retained to simplify telescoping. -/
theorem glyz_dyadic_whitney_identity (f : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ Finset.range (2 ^ N), f i) * star (∑ i ∈ Finset.range (2 ^ N), f i) =
      glyzNearEnergy f (2 ^ N) +
        ∑ n ∈ Finset.range N, glyzWhitneyEnergy (glyzDyadicBlock f N (n + 1)) (2 ^ (n + 1)) := by
  have h := glyz_dyadic_energy_telescope f N N le_rfl
  simpa only [glyzNearEnergy, Finset.range_one, Finset.sum_singleton, Nat.dist_self,
    Nat.zero_le, if_true, glyzDyadicBlock_zero, glyzDyadicBlock_finest] using h

theorem glyz_whitney_outdegree (I : Finset ℕ) (i : ℕ) :
    (I.filter (fun j => 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1)).card ≤ 4 := by
  let J : Finset ℤ := {(i : ℤ) - 3, (i : ℤ) - 2, (i : ℤ) + 2, (i : ℤ) + 3}
  have hm : Set.MapsTo (fun j : ℕ => (j : ℤ))
      (↑(I.filter (fun j => 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1)) : Set ℕ)
      (↑J : Set ℤ) := by
    intro j hj
    have hd := glyz_whitney_pair_distance (Finset.mem_filter.mp hj).2
    unfold Nat.dist at hd
    change (j : ℤ) ∈ J
    simp only [J, Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card_of_injOn _ hm (fun _ _ _ _ h => Int.ofNat_injective h)).trans
    Finset.card_le_four

theorem glyz_near_outdegree (I : Finset ℕ) (i : ℕ) :
    (I.filter (fun j => Nat.dist i j ≤ 1)).card ≤ 3 := by
  let J : Finset ℤ := {(i : ℤ) - 1, (i : ℤ), (i : ℤ) + 1}
  have hm : Set.MapsTo (fun j : ℕ => (j : ℤ))
      (↑(I.filter (fun j => Nat.dist i j ≤ 1)) : Set ℕ) (↑J : Set ℤ) := by
    intro j hj
    have hd := (Finset.mem_filter.mp hj).2
    unfold Nat.dist at hd
    change (j : ℤ) ∈ J
    simp only [J, Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card_of_injOn _ hm (fun _ _ _ _ h => Int.ofNat_injective h)).trans
    Finset.card_le_three

theorem glyz_symmetric_graph_sum_le (I : Finset ℕ) (H : ℕ → ℕ → Prop) [DecidableRel H]
    (hsym : ∀ i j, H i j ↔ H j i) (B : ℕ)
    (hdeg : ∀ i ∈ I, (I.filter (fun j => H i j)).card ≤ B)
    (W : ℕ → ℝ) (hW : ∀ i ∈ I, 0 ≤ W i) :
    (∑ i ∈ I, ∑ j ∈ I, if H i j then W i + W j else 0) ≤
      (2 * B : ℕ) * ∑ i ∈ I, W i := by
  have hfirst : (∑ i ∈ I, ∑ j ∈ I, if H i j then W i else 0) ≤
      (B : ℝ) * ∑ i ∈ I, W i := by
    calc
      _ = ∑ i ∈ I, ((I.filter (fun j => H i j)).card : ℝ) * W i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, (B : ℝ) * W i := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg i hi) (hW i hi)
      _ = _ := (Finset.mul_sum ..).symm
  have hsecond : (∑ i ∈ I, ∑ j ∈ I, if H i j then W j else 0) =
      ∑ i ∈ I, ∑ j ∈ I, if H i j then W i else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [hsym j i]
  have he : (∑ i ∈ I, ∑ j ∈ I, if H i j then W i + W j else 0) =
      (∑ i ∈ I, ∑ j ∈ I, if H i j then W i else 0) +
      ∑ i ∈ I, ∑ j ∈ I, if H i j then W j else 0 := by
    simp_rw [ite_add_zero]
    simp only [Finset.sum_add_distrib]
  rw [he, hsecond]
  push_cast
  linarith

theorem glyz_whitney_weighted_sum_le (I : Finset ℕ) (W : ℕ → ℝ) (hW : ∀ i ∈ I, 0 ≤ W i) :
    (∑ i ∈ I, ∑ j ∈ I, if 2 ≤ Nat.dist i j ∧ Nat.dist (i / 2) (j / 2) ≤ 1
      then W i + W j else 0) ≤ 8 * ∑ i ∈ I, W i := by
  apply glyz_symmetric_graph_sum_le I _ (fun i j => by rw [Nat.dist_comm i j, Nat.dist_comm (i / 2) (j / 2)])
    4 (fun i _ => glyz_whitney_outdegree I i) W hW

theorem glyz_near_weighted_sum_le (I : Finset ℕ) (W : ℕ → ℝ) (hW : ∀ i ∈ I, 0 ≤ W i) :
    (∑ i ∈ I, ∑ j ∈ I, if Nat.dist i j ≤ 1 then W i + W j else 0) ≤
      6 * ∑ i ∈ I, W i := by
  apply glyz_symmetric_graph_sum_le I _ (fun i j => by rw [Nat.dist_comm i j])
    3 (fun i _ => glyz_near_outdegree I i) W hW

end PlanarNikodym
