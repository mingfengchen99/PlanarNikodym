import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Algebra.BigOperators.Fin

/-! Factorial digit series in Wisewell's null-set construction.

Source: Laura Wisewell, *Families of surfaces lying in a null set*,
arXiv:math/0401249, §2 and Lemma 3. The symbolic digit space retains both
expansions at the ambiguous endpoints. Series on this compact space are
continuous even when the corresponding function of a real parameter is
discontinuous at an endpoint of a digit cylinder.

This file proves convergence, exact scalar cylinder bounds, and compactness
of the series graph. It does not construct the universal coefficient
schedule or assert that the graph has the required null projections. -/

noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology Nat
namespace PlanarNikodym.Wisewell

/-- The digit at position `n` is the coefficient of `1 / (n + 2)!`. -/
abbrev FactorialDigits := ∀ n : ℕ, Fin (n + 2)

abbrev FactorialPrefix (N : ℕ) := ∀ i : Fin N, Fin (i.val + 2)

def factorialPrefix (N : ℕ) (a : FactorialDigits) : FactorialPrefix N :=
  fun i => a i.val

theorem continuous_factorialPrefix (N : ℕ) : Continuous (factorialPrefix N) :=
  continuous_pi fun i => continuous_apply i.val

theorem card_factorialPrefix (N : ℕ) : Fintype.card (FactorialPrefix N) = (N + 1)! := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.factorial_succ (N + 1)]
    ring

def factorialWeight (n : ℕ) : ℝ := (n + 1 : ℝ) / (n + 2)!

theorem factorialWeight_nonneg (n : ℕ) : 0 ≤ factorialWeight n :=
  div_nonneg (by positivity) (by positivity)

theorem factorialWeight_eq_sub (n : ℕ) :
    factorialWeight n = 1 / ((n + 1)! : ℝ) - 1 / ((n + 2)! : ℝ) := by
  have hfac : ((n + 2)! : ℝ) = (n + 2 : ℝ) * ((n + 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hf : ((n + 1)! : ℝ) ≠ 0 := by positivity
  unfold factorialWeight
  rw [hfac]
  field_simp; ring

theorem summable_inv_factorial : Summable (fun n : ℕ => (1 : ℝ) / (n)!) := by
  simpa only [one_pow] using Real.summable_pow_div_factorial 1

theorem summable_factorialWeight : Summable factorialWeight := by
  have h₁ := (summable_nat_add_iff 1).2 summable_inv_factorial
  have h₂ := (summable_nat_add_iff 2).2 summable_inv_factorial
  exact (h₁.sub h₂).congr (fun n => (factorialWeight_eq_sub n).symm)

/-- Exact remaining mass after the first `N` factorial digits. -/
theorem tsum_factorialWeight_add (N : ℕ) :
    ∑' n : ℕ, factorialWeight (n + N) = 1 / ((N + 1)! : ℝ) := by
  let u : ℕ → ℝ := fun n => 1 / ((n + N + 1)! : ℝ)
  have hu : Summable u := by
    simpa only [u, Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).2 summable_inv_factorial
  have hv : Summable (fun n => u (n + 1)) := (summable_nat_add_iff 1).2 hu
  calc
    ∑' n : ℕ, factorialWeight (n + N) = ∑' n : ℕ, (u n - u (n + 1)) := by
      apply tsum_congr
      intro n
      simpa only [u, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        factorialWeight_eq_sub (n + N)
    _ = (∑' n, u n) - ∑' n, u (n + 1) := hu.tsum_sub hv
    _ = u 0 := by
      have h := hu.tsum_eq_zero_add
      linarith
    _ = 1 / ((N + 1)! : ℝ) := by simp [u]

def factorialDigitTerm (a : FactorialDigits) (n : ℕ) : ℝ :=
  (a n).val / ((n + 2)! : ℝ)

theorem factorialDigitTerm_nonneg (a : FactorialDigits) (n : ℕ) :
    0 ≤ factorialDigitTerm a n := div_nonneg (by positivity) (by positivity)

theorem factorialDigitTerm_le (a : FactorialDigits) (n : ℕ) :
    factorialDigitTerm a n ≤ factorialWeight n := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (a n).is_le

theorem norm_factorialDigitTerm_le (a : FactorialDigits) (n : ℕ) :
    ‖factorialDigitTerm a n‖ ≤ factorialWeight n := by
  rw [Real.norm_eq_abs, abs_of_nonneg (factorialDigitTerm_nonneg a n)]
  exact factorialDigitTerm_le a n

theorem summable_factorialDigitTerm (a : FactorialDigits) :
    Summable (factorialDigitTerm a) :=
  Summable.of_norm_bounded summable_factorialWeight (norm_factorialDigitTerm_le a)

def factorialValue (a : FactorialDigits) : ℝ := ∑' n, factorialDigitTerm a n

theorem continuous_factorialDigitTerm (n : ℕ) :
    Continuous (fun a => factorialDigitTerm a n) := by
  have hc : Continuous (fun k : Fin (n + 2) => (k.val : ℝ)) :=
    continuous_of_discreteTopology
  exact (hc.comp (continuous_apply n)).div_const _

theorem continuous_factorialValue : Continuous factorialValue :=
  continuous_tsum continuous_factorialDigitTerm summable_factorialWeight
    (fun n a => norm_factorialDigitTerm_le a n)

theorem factorialValue_mem_Icc (a : FactorialDigits) : factorialValue a ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact tsum_nonneg (factorialDigitTerm_nonneg a)
  · calc
      factorialValue a ≤ ∑' n, factorialWeight n :=
        (summable_factorialDigitTerm a).tsum_le_tsum (factorialDigitTerm_le a) summable_factorialWeight
      _ = 1 := by simpa using tsum_factorialWeight_add 0

/-- The sharp scalar part of Wisewell's cylinder estimate: two sequences
with the same first `N` digits represent numbers at distance at most
`1 / (N + 1)!`. No uniqueness of the real expansion is used. -/
theorem norm_factorialValue_sub_le_of_prefix_eq (a b : FactorialDigits) (N : ℕ)
    (hab : factorialPrefix N a = factorialPrefix N b) :
    ‖factorialValue a - factorialValue b‖ ≤ 1 / ((N + 1)! : ℝ) := by
  have hprefix : ∑ n ∈ range N, factorialDigitTerm a n =
      ∑ n ∈ range N, factorialDigitTerm b n := by
    apply Finset.sum_congr rfl
    intro n hn
    have he := congrFun hab (⟨n, mem_range.mp hn⟩ : Fin N)
    exact congrArg (fun k : Fin (n + 2) => k.val / ((n + 2)! : ℝ)) he
  have ha := (summable_factorialDigitTerm a).sum_add_tsum_nat_add N
  have hb := (summable_factorialDigitTerm b).sum_add_tsum_nat_add N
  have hs₁ : Summable (fun n => factorialDigitTerm a (n + N)) :=
    (summable_nat_add_iff N).2 (summable_factorialDigitTerm a)
  have hs₂ : Summable (fun n => factorialDigitTerm b (n + N)) :=
    (summable_nat_add_iff N).2 (summable_factorialDigitTerm b)
  have hdiff : factorialValue a - factorialValue b =
      ∑' n, (factorialDigitTerm a (n + N) - factorialDigitTerm b (n + N)) := by
    rw [hs₁.tsum_sub hs₂]
    change (∑' n, factorialDigitTerm a n) - (∑' n, factorialDigitTerm b n) = _
    rw [← ha, ← hb, hprefix]
    ring
  have hbound (n : ℕ) :
      ‖factorialDigitTerm a (n + N) - factorialDigitTerm b (n + N)‖ ≤ factorialWeight (n + N) := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [factorialDigitTerm_nonneg a (n + N), factorialDigitTerm_le b (n + N)]
    · linarith [factorialDigitTerm_nonneg b (n + N), factorialDigitTerm_le a (n + N)]
  rw [hdiff]
  calc
    ‖∑' n, (factorialDigitTerm a (n + N) - factorialDigitTerm b (n + N))‖ ≤
        ∑' n, ‖factorialDigitTerm a (n + N) - factorialDigitTerm b (n + N)‖ :=
      norm_tsum_le_tsum_norm (hs₁.sub hs₂).norm
    _ ≤ ∑' n, factorialWeight (n + N) :=
      (hs₁.sub hs₂).norm.tsum_le_tsum hbound
        ((summable_nat_add_iff N).2 summable_factorialWeight)
    _ = 1 / ((N + 1)! : ℝ) := tsum_factorialWeight_add N

end PlanarNikodym.Wisewell
