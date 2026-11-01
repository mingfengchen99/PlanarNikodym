import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Exact cancellation in GLYZ's finite real exponent system (4.5).
Finiteness and the recursive inequalities remain explicit hypotheses:
this algebraic theorem does not assert the analytic lower-degree gain. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

theorem glyz_bootstrap_sum_identity (A : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (A (N - i) / ((i : ℝ) + 1) +
      ((N - i : ℕ) : ℝ) / ((N - i : ℕ) + 1 : ℝ) * A i - A (i + 1))) =
        (N : ℝ) / ((N : ℝ) + 1) * A 0 := by
  let T : ℕ → ℝ := fun i => ((N - i : ℕ) : ℝ) / ((N - i : ℕ) + 1 : ℝ) * A i
  have href : (∑ i ∈ Finset.range N, A (N - i) / ((i : ℝ) + 1)) =
      ∑ i ∈ Finset.range N, A (i + 1) / ((N - i : ℕ) : ℝ) := by
    rw [← Finset.sum_range_reflect (fun i => A (N - i) / ((i : ℝ) + 1)) N]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < N := Finset.mem_range.mp hi
    have h₁ : N - (N - 1 - i) = i + 1 := by omega
    have h₂ : N - 1 - i + 1 = N - i := by omega
    rw [h₁]
    have h₂' : ((N - 1 - i : ℕ) : ℝ) + 1 = ((N - i : ℕ) : ℝ) := by exact_mod_cast h₂
    rw [h₂']
  have hterm (i : ℕ) (hi : i < N) :
      A (i + 1) / ((N - i : ℕ) : ℝ) + T i - A (i + 1) = T i - T (i + 1) := by
    have hn : N - i = (N - (i + 1)) + 1 := by omega
    dsimp [T]
    rw [hn]
    push_cast
    field_simp
    ring
  calc
    _ = (∑ i ∈ Finset.range N, A (N - i) / ((i : ℝ) + 1)) +
        (∑ i ∈ Finset.range N, T i) - ∑ i ∈ Finset.range N, A (i + 1) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, T]
    _ = ∑ i ∈ Finset.range N, (T i - T (i + 1)) := by
      rw [href, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i hi => hterm i (Finset.mem_range.mp hi)
    _ = T 0 - T N := Finset.sum_range_sub' T N
    _ = _ := by simp [T]

theorem glyz_finite_bootstrap_nonpos {N : ℕ} (hN : 0 < N) (A : ℕ → ℝ)
    (h : ∀ i < N, A (N - i) / ((i : ℝ) + 1) +
      ((N - i : ℕ) : ℝ) / ((N - i : ℕ) + 1 : ℝ) * A i ≤ A (i + 1)) :
    A 0 ≤ 0 := by
  have hs : (∑ i ∈ Finset.range N, (A (N - i) / ((i : ℝ) + 1) +
      ((N - i : ℕ) : ℝ) / ((N - i : ℕ) + 1 : ℝ) * A i - A (i + 1))) ≤ 0 :=
    Finset.sum_nonpos fun i hi => sub_nonpos.mpr (h i (Finset.mem_range.mp hi))
  rw [glyz_bootstrap_sum_identity] at hs
  have hc : 0 < (N : ℝ) / ((N : ℝ) + 1) := by positivity
  nlinarith

theorem glyz_finite_bootstrap_zero {N : ℕ} (hN : 0 < N) (A : ℕ → ℝ) (hA : 0 ≤ A 0)
    (h : ∀ i < N, A (N - i) / ((i : ℝ) + 1) +
      ((N - i : ℕ) : ℝ) / ((N - i : ℕ) + 1 : ℝ) * A i ≤ A (i + 1)) : A 0 = 0 :=
  le_antisymm (glyz_finite_bootstrap_nonpos hN A h) hA

end PlanarNikodym
