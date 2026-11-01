import PlanarNikodym.Projection.BoundedFactorialSelector

noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology Nat
namespace PlanarNikodym.Wisewell

def factorialPrefixExtend (N : ℕ) (p : FactorialPrefix N) : FactorialDigits :=
  fun n => if h : n < N then p ⟨n, h⟩ else 0

@[simp] theorem factorialPrefix_extend (N : ℕ) (p : FactorialPrefix N) :
    factorialPrefix N (factorialPrefixExtend N p) = p := by
  ext i
  simp [factorialPrefix, factorialPrefixExtend, i.is_lt]

theorem factorialPrefix_eq_of_le {k N : ℕ} (hkN : k ≤ N) {a b : FactorialDigits}
    (hab : factorialPrefix N a = factorialPrefix N b) : factorialPrefix k a = factorialPrefix k b := by
  ext i
  exact congrArg Fin.val (congrFun hab (⟨i.val, lt_of_lt_of_le i.is_lt hkN⟩ : Fin N))

theorem factorialDigitTerm_congr_of_prefix_eq {a b : FactorialDigits} {N n : ℕ}
    (hab : factorialPrefix N a = factorialPrefix N b) (hn : n < N) :
    factorialDigitTerm a n = factorialDigitTerm b n := by
  have he := congrFun hab (⟨n, hn⟩ : Fin N)
  exact congrArg (fun k : Fin (n + 2) => k.val / ((n + 2)! : ℝ)) he

theorem factorialSelectorTerm_congr_of_prefix_eq
    (r : ∀ n, FactorialPrefix n → ℝ) {a b : FactorialDigits} {N n : ℕ}
    (hab : factorialPrefix N a = factorialPrefix N b) (hn : n < N) :
    factorialSelectorTerm r a n = factorialSelectorTerm r b n := by
  rw [factorialSelectorTerm, factorialSelectorTerm,
    factorialPrefix_eq_of_le (Nat.le_of_lt hn) hab,
    factorialDigitTerm_congr_of_prefix_eq hab hn]

theorem factorialDigitTerm_extend_zero (N : ℕ) (p : FactorialPrefix N)
    (n : ℕ) (hn : N ≤ n) : factorialDigitTerm (factorialPrefixExtend N p) n = 0 := by
  simp [factorialDigitTerm, factorialPrefixExtend, not_lt.mpr hn]

theorem factorialSelectorTerm_extend_zero (r : ∀ n, FactorialPrefix n → ℝ)
    (N : ℕ) (p : FactorialPrefix N) (n : ℕ) (hn : N ≤ n) :
    factorialSelectorTerm r (factorialPrefixExtend N p) n = 0 := by
  rw [factorialSelectorTerm, factorialDigitTerm_extend_zero N p n hn, mul_zero]

theorem factorialValue_prefixExtend (N : ℕ) (a : FactorialDigits) :
    factorialValue (factorialPrefixExtend N (factorialPrefix N a)) =
      ∑ n ∈ range N, factorialDigitTerm a n := by
  let b := factorialPrefixExtend N (factorialPrefix N a)
  have hab : factorialPrefix N b = factorialPrefix N a := factorialPrefix_extend N _
  have h := (summable_factorialDigitTerm b).sum_add_tsum_nat_add N
  have hz : (∑' n, factorialDigitTerm b (n + N)) = 0 := by
    calc
      _ = ∑' _n : ℕ, (0 : ℝ) := tsum_congr fun n =>
        factorialDigitTerm_extend_zero N _ (n + N) (Nat.le_add_left _ _)
      _ = 0 := tsum_zero
  rw [hz, add_zero] at h
  change (∑' n, factorialDigitTerm b n) = _
  rw [← h]
  exact Finset.sum_congr rfl (fun n hn => factorialDigitTerm_congr_of_prefix_eq hab (mem_range.mp hn))

theorem factorialSelector_prefixExtend
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (N : ℕ) (a : FactorialDigits) :
    factorialSelector r (factorialPrefixExtend N (factorialPrefix N a)) =
      ∑ n ∈ range N, factorialSelectorTerm r a n := by
  let b := factorialPrefixExtend N (factorialPrefix N a)
  have hab : factorialPrefix N b = factorialPrefix N a := factorialPrefix_extend N _
  have h := (summable_factorialSelectorTerm_of_bounded r M hM hr b).sum_add_tsum_nat_add N
  have hz : (∑' n, factorialSelectorTerm r b (n + N)) = 0 := by
    calc
      _ = ∑' _n : ℕ, (0 : ℝ) := tsum_congr fun n =>
        factorialSelectorTerm_extend_zero r N _ (n + N) (Nat.le_add_left _ _)
      _ = 0 := tsum_zero
  rw [hz, add_zero] at h
  change (∑' n, factorialSelectorTerm r b n) = _
  rw [← h]
  exact Finset.sum_congr rfl (fun n hn => factorialSelectorTerm_congr_of_prefix_eq r hab (mem_range.mp hn))

def factorialPoint (r : ∀ n, FactorialPrefix n → ℝ) (a : FactorialDigits) : Plane :=
  (factorialValue a, factorialSelector r a)

def prefixFactorialPoint (r : ∀ n, FactorialPrefix n → ℝ) (N : ℕ)
    (p : FactorialPrefix N) : Plane := factorialPoint r (factorialPrefixExtend N p)

theorem factorialPoint_mem_rectangle
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) :
    factorialPoint r a ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-M) M := by
  exact ⟨factorialValue_mem_Icc a, abs_le.mp (norm_factorialSelector_le_of_bounded r M hM hr a)⟩

theorem norm_factorialPoint_sub_prefix_le
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) (N : ℕ) :
    ‖factorialPoint r a - prefixFactorialPoint r N (factorialPrefix N a)‖ ≤
      max 1 M / ((N + 1)! : ℝ) := by
  rw [Prod.norm_def]
  apply max_le
  · change ‖factorialValue a - factorialValue (factorialPrefixExtend N (factorialPrefix N a))‖ ≤ _
    exact (norm_factorialValue_sub_le_of_prefix_eq a _ N (factorialPrefix_extend N _).symm).trans
      (div_le_div_of_nonneg_right (le_max_left 1 M) (by positivity))
  · change ‖factorialSelector r a - factorialSelector r (factorialPrefixExtend N (factorialPrefix N a))‖ ≤ _
    rw [factorialSelector_prefixExtend r M hM hr N a]
    exact (norm_factorialSelector_sub_sum_le_of_bounded r M hM hr a N).trans
      (div_le_div_of_nonneg_right (le_max_right 1 M) (by positivity))

end PlanarNikodym.Wisewell
