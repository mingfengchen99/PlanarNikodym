import PlanarNikodym.Projection.FactorialDigitSeries
import Mathlib.Algebra.Order.Floor.Semifield

/-! An actual factorial expansion for every parameter in the unit interval.
The symbolic model deliberately does not choose between the two expansions
at terminating endpoints. -/

noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology Nat
namespace PlanarNikodym.Wisewell

def greedyFactorialDigits (y : ℝ) : FactorialDigits := fun n =>
  ⟨⌊((n + 2)! : ℝ) * y⌋₊ % (n + 2), Nat.mod_lt _ (by omega)⟩

theorem greedyFactorialDigitTerm_eq_sub (y : ℝ) (n : ℕ) :
    factorialDigitTerm (greedyFactorialDigits y) n =
      (⌊((n + 2)! : ℝ) * y⌋₊ : ℝ) / ((n + 2)! : ℝ) -
        (⌊((n + 1)! : ℝ) * y⌋₊ : ℝ) / ((n + 1)! : ℝ) := by
  have hfac : ((n + 2)! : ℝ) = (n + 2 : ℝ) * ((n + 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hf : ((n + 1)! : ℝ) ≠ 0 := by positivity
  have hdiv : ⌊((n + 2)! : ℝ) * y⌋₊ / (n + 2) = ⌊((n + 1)! : ℝ) * y⌋₊ := by
    rw [← Nat.floor_div_natCast]
    congr 1
    rw [hfac]
    field_simp
    push_cast
    ring
  have hmod : ((⌊((n + 2)! : ℝ) * y⌋₊ % (n + 2) : ℕ) : ℝ) =
      (⌊((n + 2)! : ℝ) * y⌋₊ : ℝ) -
        (n + 2 : ℝ) * (⌊((n + 1)! : ℝ) * y⌋₊ : ℝ) := by
    have h := Nat.mod_add_div ⌊((n + 2)! : ℝ) * y⌋₊ (n + 2)
    rw [hdiv] at h
    have hc : ((⌊((n + 2)! : ℝ) * y⌋₊ % (n + 2) : ℕ) : ℝ) +
        (n + 2 : ℝ) * (⌊((n + 1)! : ℝ) * y⌋₊ : ℝ) =
          (⌊((n + 2)! : ℝ) * y⌋₊ : ℝ) := by exact_mod_cast h
    linarith
  change ((⌊((n + 2)! : ℝ) * y⌋₊ % (n + 2) : ℕ) : ℝ) / ((n + 2)! : ℝ) = _
  rw [hmod, hfac]
  field_simp

theorem sum_greedyFactorialDigitTerm (y : ℝ) (N : ℕ) :
    ∑ n ∈ range N, factorialDigitTerm (greedyFactorialDigits y) n =
      (⌊((N + 1)! : ℝ) * y⌋₊ : ℝ) / ((N + 1)! : ℝ) - (⌊y⌋₊ : ℝ) := by
  simp_rw [greedyFactorialDigitTerm_eq_sub]
  simpa using (Finset.sum_range_sub
    (fun n : ℕ => (⌊((n + 1)! : ℝ) * y⌋₊ : ℝ) / ((n + 1)! : ℝ)) N)

/-- Greedy factorial digits represent every parameter in `[0,1)`. -/
theorem factorialValue_greedyFactorialDigits {y : ℝ} (hy : 0 ≤ y) (hy₁ : y < 1) :
    factorialValue (greedyFactorialDigits y) = y := by
  have hfloor : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy₁
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right N 1) tendsto_id
  have hfac : Tendsto (fun N : ℕ => ((N + 1)! : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (factorial_tendsto_atTop.comp hshift)
  have hlim : Tendsto
      (fun N : ℕ => (⌊((N + 1)! : ℝ) * y⌋₊ : ℝ) / ((N + 1)! : ℝ)) atTop (𝓝 y) := by
    simpa only [Function.comp_def, mul_comm] using (tendsto_nat_floor_mul_div_atTop hy).comp hfac
  have hpartial : Tendsto (fun N => ∑ n ∈ range N, factorialDigitTerm (greedyFactorialDigits y) n)
      atTop (𝓝 y) := by
    simpa only [sum_greedyFactorialDigitTerm, hfloor, Nat.cast_zero, sub_zero] using hlim
  exact tendsto_nhds_unique
    (summable_factorialDigitTerm (greedyFactorialDigits y)).hasSum.tendsto_sum_nat hpartial

def maximalFactorialDigits : FactorialDigits := fun n => ⟨n + 1, by omega⟩

theorem factorialValue_maximalFactorialDigits : factorialValue maximalFactorialDigits = 1 := by
  simpa only [factorialValue, factorialDigitTerm, maximalFactorialDigits, factorialWeight,
    Nat.add_zero, Nat.zero_add, Nat.cast_add, Nat.cast_one, Nat.factorial_one, div_one]
      using tsum_factorialWeight_add 0

/-- The compact symbolic digit space parametrizes the entire unit interval. -/
theorem range_factorialValue : range factorialValue = Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro y ⟨a, rfl⟩
    exact factorialValue_mem_Icc a
  · intro y hy
    by_cases h : y = 1
    · exact ⟨maximalFactorialDigits, factorialValue_maximalFactorialDigits.trans h.symm⟩
    · exact ⟨greedyFactorialDigits y,
        factorialValue_greedyFactorialDigits hy.1 (lt_of_le_of_ne hy.2 h)⟩

end PlanarNikodym.Wisewell
