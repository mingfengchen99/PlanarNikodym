import PlanarNikodym.Analysis.Maximal.E2SeeleyScaledBlocks
import Mathlib.Analysis.SpecificLimits.Normed

/-! An actual Seeley moment sequence, constructed by successively
correcting moments with the scaled finite Lagrange blocks. Every absolute
weighted moment is summable; every signed moment equals one. -/
noncomputable section
open scoped BigOperators
namespace PlanarNikodym

def e2SeeleyPartialMoments : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun j =>
      let e := 1 - e2SeeleyPartialMoments n n
      let R := e2SeeleyBlockScale n e
      e2SeeleyPartialMoments n j + ∑ k : Fin (n + 1),
        e2SeeleyScaledCoefficient n e R k * (e2SeeleyScaledNode n R k) ^ j

def e2SeeleyError (n : ℕ) : ℝ := 1 - e2SeeleyPartialMoments n n
def e2SeeleyScale (n : ℕ) : ℝ := e2SeeleyBlockScale n (e2SeeleyError n)
def e2SeeleyCoefficient (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  e2SeeleyScaledCoefficient n (e2SeeleyError n) (e2SeeleyScale n) k
def e2SeeleyReflectionNode (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  e2SeeleyScaledNode n (e2SeeleyScale n) k

theorem e2SeeleyPartialMoments_succ (n j : ℕ) :
    e2SeeleyPartialMoments (n + 1) j = e2SeeleyPartialMoments n j +
      ∑ k : Fin (n + 1), e2SeeleyCoefficient n k * (e2SeeleyReflectionNode n k) ^ j := rfl

theorem e2SeeleyCoefficient_low (n j : ℕ) (hj : j < n) :
    ∑ k : Fin (n + 1), e2SeeleyCoefficient n k * (e2SeeleyReflectionNode n k) ^ j = 0 :=
  e2SeeleyScaledCoefficient_low n j hj _ _

theorem e2SeeleyCoefficient_top (n : ℕ) :
    ∑ k : Fin (n + 1), e2SeeleyCoefficient n k * (e2SeeleyReflectionNode n k) ^ n = e2SeeleyError n :=
  e2SeeleyScaledCoefficient_top n _ _ (e2SeeleyBlockScale_pos n _).ne'

theorem e2SeeleyPartialMoments_correct (n j : ℕ) (hj : j < n) : e2SeeleyPartialMoments n j = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [e2SeeleyPartialMoments_succ]
    by_cases h : j = n
    · subst j
      rw [e2SeeleyCoefficient_top]
      simp [e2SeeleyError]
    · rw [e2SeeleyCoefficient_low n j (by omega), ih (by omega), add_zero]

theorem e2SeeleyPartialMoments_eq_sum (n j : ℕ) :
    e2SeeleyPartialMoments n j = ∑ m ∈ Finset.range n,
      ∑ k : Fin (m + 1), e2SeeleyCoefficient m k * (e2SeeleyReflectionNode m k) ^ j := by
  induction n with
  | zero => simp [e2SeeleyPartialMoments]
  | succ n ih => rw [e2SeeleyPartialMoments_succ, Finset.sum_range_succ, ih]

/-- Every moment equals the value at the continuation point +1. -/
theorem e2SeeleyCoefficient_all_moments (j : ℕ) :
    ∑' n, ∑ k : Fin (n + 1), e2SeeleyCoefficient n k * (e2SeeleyReflectionNode n k) ^ j = 1 := by
  rw [tsum_eq_sum (s := Finset.range (j + 1)) (fun n hn =>
    e2SeeleyCoefficient_low n j (by
      have hh : j + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      omega))]
  rw [← e2SeeleyPartialMoments_eq_sum]
  exact e2SeeleyPartialMoments_correct (j + 1) j (Nat.lt_succ_self j)

theorem e2SeeleyCoefficient_absolute_moment_nonneg (n j : ℕ) :
    0 ≤ ∑ k : Fin (n + 1), |e2SeeleyCoefficient n k| * |e2SeeleyReflectionNode n k| ^ j := by
  positivity

theorem e2SeeleyCoefficient_absolute_moment_bound (n j : ℕ) (hj : j < n) :
    ∑ k : Fin (n + 1), |e2SeeleyCoefficient n k| * |e2SeeleyReflectionNode n k| ^ j ≤
      ((2 : ℝ) ^ n)⁻¹ := e2SeeleyScaledCoefficient_lower_mass n j hj _

/-- The bounds control absolute moments, so the construction is suitable
for uniform convergence of every derivative, not merely formal moments. -/
theorem e2SeeleyCoefficient_summable_absolute_moments (j : ℕ) :
    Summable (fun n => ∑ k : Fin (n + 1),
      |e2SeeleyCoefficient n k| * |e2SeeleyReflectionNode n k| ^ j) := by
  have hgeo : Summable (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) := by
    simpa only [inv_pow] using
      (summable_geometric_of_abs_lt_one (by norm_num : |(2 : ℝ)⁻¹| < 1))
  apply Summable.of_norm_bounded_eventually hgeo
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_atTop.2 ⟨j + 1, fun n hn => hn⟩] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (e2SeeleyCoefficient_absolute_moment_nonneg n j)]
  exact e2SeeleyCoefficient_absolute_moment_bound n j (by omega)

theorem e2SeeleyReflectionNode_neg (n : ℕ) (k : Fin (n + 1)) : e2SeeleyReflectionNode n k < 0 :=
  mul_neg_of_pos_of_neg (e2SeeleyBlockScale_pos n _) (e2SeeleyNode_neg n k)

theorem e2SeeleyReflectionNode_abs_ge_index (n : ℕ) (k : Fin (n + 1)) :
    (n : ℝ) + 1 ≤ |e2SeeleyReflectionNode n k| := by
  have hR := e2SeeleyBlockScale_pos n (e2SeeleyError n)
  have hv : 1 ≤ |e2SeeleyNode n k| := by
    rw [abs_of_neg (e2SeeleyNode_neg n k)]
    unfold e2SeeleyNode
    have hk : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ e2SeeleyScale n := e2SeeleyBlockScale_ge_index n _
    _ ≤ e2SeeleyScale n * |e2SeeleyNode n k| := le_mul_of_one_le_right hR.le hv
    _ = _ := by simp only [e2SeeleyReflectionNode, e2SeeleyScaledNode, abs_mul, e2SeeleyScale,
      abs_of_pos hR]

end PlanarNikodym
