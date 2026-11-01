import PlanarNikodym.Projection.FactorialPrefixTruncation

noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology Nat
namespace PlanarNikodym.Wisewell

theorem prefixFactorialPoint_succ_sub
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) (N : ℕ) :
    prefixFactorialPoint r (N + 1) (factorialPrefix (N + 1) a) -
      prefixFactorialPoint r N (factorialPrefix N a) =
        (factorialDigitTerm a N, factorialSelectorTerm r a N) := by
  apply Prod.ext
  · change factorialValue (factorialPrefixExtend (N + 1) (factorialPrefix (N + 1) a)) -
      factorialValue (factorialPrefixExtend N (factorialPrefix N a)) = _
    rw [factorialValue_prefixExtend, factorialValue_prefixExtend, sum_range_succ]
    ring
  · change factorialSelector r (factorialPrefixExtend (N + 1) (factorialPrefix (N + 1) a)) -
      factorialSelector r (factorialPrefixExtend N (factorialPrefix N a)) = _
    rw [factorialSelector_prefixExtend r M hM hr,
      factorialSelector_prefixExtend r M hM hr, sum_range_succ]
    ring

theorem norm_prefixFactorialPoint_sub_earlier_le
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) (k N : ℕ) (hkN : k ≤ N) :
    ‖prefixFactorialPoint r N (factorialPrefix N a) -
      prefixFactorialPoint r k (factorialPrefix k a)‖ ≤ max 1 M / ((k + 1)! : ℝ) := by
  let b := factorialPrefixExtend N (factorialPrefix N a)
  have hpre : factorialPrefix k b = factorialPrefix k a :=
    factorialPrefix_eq_of_le hkN (factorialPrefix_extend N _)
  have h := norm_factorialPoint_sub_prefix_le r M hM hr b k
  rw [hpre] at h
  exact h

theorem linear_apply_pair (A : Plane →L[ℝ] ℝ) (u v : ℝ) :
    A (u, v) = u * A (1, 0) + v * A (0, 1) := by
  have he : (u, v) = u • ((1, 0) : Plane) + v • ((0, 1) : Plane) := by
    ext <;> simp
  rw [he, map_add, map_smul, map_smul]
  rfl

/-- Principal coefficient cancellation plus one extra factorial digit
controls the entire linearized remainder. The second term is smaller by
the additional factor `N + 2`. -/
theorem norm_linear_factorialPoint_tail_le
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) (N : ℕ)
    (A : Plane →L[ℝ] ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hcoef : ‖A (1, 0) + A (0, 1) * r N (factorialPrefix N a)‖ ≤ η) :
    ‖A (factorialPoint r a - prefixFactorialPoint r N (factorialPrefix N a))‖ ≤
      η / ((N + 1)! : ℝ) + ‖A‖ * max 1 M / ((N + 2)! : ℝ) := by
  let x := factorialPoint r a
  let xN := prefixFactorialPoint r N (factorialPrefix N a)
  let xS := prefixFactorialPoint r (N + 1) (factorialPrefix (N + 1) a)
  have he : x - xN = (x - xS) +
      (factorialDigitTerm a N, factorialSelectorTerm r a N) := by
    rw [← prefixFactorialPoint_succ_sub r M hM hr a N]
    change x - xN = (x - xS) + (xS - xN)
    abel
  have hd : ‖factorialDigitTerm a N‖ ≤ 1 / ((N + 1)! : ℝ) := by
    apply (norm_factorialDigitTerm_le a N).trans
    rw [factorialWeight_eq_sub]
    exact sub_le_self _ (by positivity)
  have hmain : ‖A (factorialDigitTerm a N, factorialSelectorTerm r a N)‖ ≤
      η / ((N + 1)! : ℝ) := by
    have heA : A (factorialDigitTerm a N, factorialSelectorTerm r a N) =
        (A (1, 0) + A (0, 1) * r N (factorialPrefix N a)) * factorialDigitTerm a N := by
      rw [linear_apply_pair, factorialSelectorTerm]
      ring
    rw [heA, norm_mul, div_eq_mul_inv]
    exact mul_le_mul hcoef (by simpa only [one_div] using hd) (norm_nonneg _) hη
  have htail : ‖A (x - xS)‖ ≤ ‖A‖ * max 1 M / ((N + 2)! : ℝ) := by
    calc
      ‖A (x - xS)‖ ≤ ‖A‖ * ‖x - xS‖ := A.le_opNorm _
      _ ≤ ‖A‖ * (max 1 M / ((N + 2)! : ℝ)) :=
        mul_le_mul_of_nonneg_left (norm_factorialPoint_sub_prefix_le r M hM hr a (N + 1)) (norm_nonneg _)
      _ = _ := by ring
  change ‖A (x - xN)‖ ≤ _
  rw [he, map_add]
  exact (norm_add_le _ _).trans (by linarith)

end PlanarNikodym.Wisewell
