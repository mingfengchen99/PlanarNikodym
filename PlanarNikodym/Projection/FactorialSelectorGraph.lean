import PlanarNikodym.Projection.FactorialDigitSeries

/-! The compact symbolic graph underlying a factorial selector.

Coefficient functions depend on finite digit prefixes. A crude linear
growth bound already gives uniform convergence and a compact graph; the
coefficient schedule and cancellation needed for nullity are proved
in FactorialCoefficientSchedule and FactorialNullSlices. -/

noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology Nat
namespace PlanarNikodym.Wisewell

theorem linear_mul_factorialWeight (n : ℕ) :
    (n + 2 : ℝ) * factorialWeight n = 1 / ((n)! : ℝ) := by
  have hfac : ((n + 2)! : ℝ) = (n + 2 : ℝ) * (n + 1 : ℝ) * ((n)! : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have h₁ : (n + 1 : ℝ) ≠ 0 := by positivity
  have h₂ : (n + 2 : ℝ) ≠ 0 := by positivity
  have hf : ((n)! : ℝ) ≠ 0 := by positivity
  unfold factorialWeight
  rw [hfac]
  field_simp

def factorialSelectorTerm (r : ∀ n, FactorialPrefix n → ℝ)
    (a : FactorialDigits) (n : ℕ) : ℝ :=
  r n (factorialPrefix n a) * factorialDigitTerm a n

def factorialSelector (r : ∀ n, FactorialPrefix n → ℝ)
    (a : FactorialDigits) : ℝ := ∑' n, factorialSelectorTerm r a n

theorem norm_factorialSelectorTerm_le_inv_factorial
    (r : ∀ n, FactorialPrefix n → ℝ)
    (hr : ∀ n p, ‖r n p‖ ≤ (n + 2 : ℝ)) (a : FactorialDigits) (n : ℕ) :
    ‖factorialSelectorTerm r a n‖ ≤ 1 / ((n)! : ℝ) := by
  rw [factorialSelectorTerm, norm_mul]
  calc
    ‖r n (factorialPrefix n a)‖ * ‖factorialDigitTerm a n‖ ≤
        (n + 2 : ℝ) * factorialWeight n :=
      mul_le_mul (hr n _) (norm_factorialDigitTerm_le a n) (norm_nonneg _) (by positivity)
    _ = 1 / ((n)! : ℝ) := linear_mul_factorialWeight n

theorem summable_factorialSelectorTerm
    (r : ∀ n, FactorialPrefix n → ℝ)
    (hr : ∀ n p, ‖r n p‖ ≤ (n + 2 : ℝ)) (a : FactorialDigits) :
    Summable (factorialSelectorTerm r a) :=
  Summable.of_norm_bounded summable_inv_factorial
    (norm_factorialSelectorTerm_le_inv_factorial r hr a)

theorem continuous_factorialSelectorTerm
    (r : ∀ n, FactorialPrefix n → ℝ) (n : ℕ) :
    Continuous (fun a => factorialSelectorTerm r a n) := by
  have hc : Continuous (r n) := continuous_of_discreteTopology
  exact (hc.comp (continuous_factorialPrefix n)).mul (continuous_factorialDigitTerm n)

theorem continuous_factorialSelector
    (r : ∀ n, FactorialPrefix n → ℝ)
    (hr : ∀ n p, ‖r n p‖ ≤ (n + 2 : ℝ)) :
    Continuous (factorialSelector r) :=
  continuous_tsum (continuous_factorialSelectorTerm r) summable_inv_factorial
    (fun n a => norm_factorialSelectorTerm_le_inv_factorial r hr a n)

theorem norm_factorialSelectorTerm_le_of_bounded
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) (n : ℕ) :
    ‖factorialSelectorTerm r a n‖ ≤ M * factorialWeight n := by
  rw [factorialSelectorTerm, norm_mul]
  exact mul_le_mul (hr n _) (norm_factorialDigitTerm_le a n) (norm_nonneg _) hM

theorem summable_factorialSelectorTerm_of_bounded
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) :
    Summable (factorialSelectorTerm r a) :=
  Summable.of_norm_bounded (summable_factorialWeight.mul_left M)
    (norm_factorialSelectorTerm_le_of_bounded r M hM hr a)

/-- Bounded coefficient schedules suffice for a selector adapted to a
single local smooth family. Their full symbolic series stays bounded by
the same constant. -/
theorem norm_factorialSelector_le_of_bounded
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) :
    ‖factorialSelector r a‖ ≤ M := by
  have hs := summable_factorialSelectorTerm_of_bounded r M hM hr a
  calc
    ‖factorialSelector r a‖ ≤ ∑' n, ‖factorialSelectorTerm r a n‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n, M * factorialWeight n :=
      hs.norm.tsum_le_tsum (norm_factorialSelectorTerm_le_of_bounded r M hM hr a)
        (summable_factorialWeight.mul_left M)
    _ = M := by
      rw [tsum_mul_left]
      have hw : (∑' n, factorialWeight n) = 1 := by simpa using tsum_factorialWeight_add 0
      rw [hw, mul_one]

theorem continuous_factorialSelector_of_bounded
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) : Continuous (factorialSelector r) :=
  continuous_tsum (continuous_factorialSelectorTerm r) (summable_factorialWeight.mul_left M)
    (fun n a => norm_factorialSelectorTerm_le_of_bounded r M hM hr a n)

/-- The precise truncation bound used by the bounded-coefficient version
of Wisewell's error decomposition. -/
theorem norm_factorialSelector_sub_sum_le_of_bounded
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (a : FactorialDigits) (N : ℕ) :
    ‖factorialSelector r a - ∑ n ∈ range N, factorialSelectorTerm r a n‖ ≤
      M / ((N + 1)! : ℝ) := by
  have hs := summable_factorialSelectorTerm_of_bounded r M hM hr a
  have htail : Summable (fun n => factorialSelectorTerm r a (n + N)) :=
    (summable_nat_add_iff N).2 hs
  have he : factorialSelector r a - ∑ n ∈ range N, factorialSelectorTerm r a n =
      ∑' n, factorialSelectorTerm r a (n + N) := by
    have h := hs.sum_add_tsum_nat_add N
    change (∑' n, factorialSelectorTerm r a n) - _ = _
    linarith
  rw [he]
  calc
    ‖∑' n, factorialSelectorTerm r a (n + N)‖ ≤ ∑' n, ‖factorialSelectorTerm r a (n + N)‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n, M * factorialWeight (n + N) :=
      htail.norm.tsum_le_tsum (fun n => norm_factorialSelectorTerm_le_of_bounded r M hM hr a (n + N))
        (((summable_nat_add_iff N).2 summable_factorialWeight).mul_left M)
    _ = M / ((N + 1)! : ℝ) := by rw [tsum_mul_left, tsum_factorialWeight_add]; ring

/-- Both endpoint expansions are retained, so this symbolic graph can
be compact even when a chosen real-parameter selector has jumps. -/
def factorialSeriesGraph (r : ∀ n, FactorialPrefix n → ℝ) : Set Plane :=
  (fun a => (factorialValue a, factorialSelector r a)) '' univ

theorem isCompact_factorialSeriesGraph
    (r : ∀ n, FactorialPrefix n → ℝ)
    (hr : ∀ n p, ‖r n p‖ ≤ (n + 2 : ℝ)) :
    IsCompact (factorialSeriesGraph r) :=
  isCompact_univ.image (continuous_factorialValue.prodMk (continuous_factorialSelector r hr))

theorem measurableSet_factorialSeriesGraph
    (r : ∀ n, FactorialPrefix n → ℝ)
    (hr : ∀ n p, ‖r n p‖ ≤ (n + 2 : ℝ)) :
    MeasurableSet (factorialSeriesGraph r) :=
  (isCompact_factorialSeriesGraph r hr).measurableSet

theorem isCompact_factorialSeriesGraph_of_bounded
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) : IsCompact (factorialSeriesGraph r) :=
  isCompact_univ.image
    (continuous_factorialValue.prodMk (continuous_factorialSelector_of_bounded r M hM hr))

def factorialSeriesSweep (r : ∀ n, FactorialPrefix n → ℝ)
    (f : ℝ × Plane → ℝ) (K : Set ℝ) : Set Plane :=
  (fun p : ℝ × Plane => (p.1, f p)) '' (K ×ˢ factorialSeriesGraph r)

/-- For the jointly continuous families used in the present project,
the symbolic factorial construction gives an actual compact sweep.
This avoids a general Souslin-measurability argument for this step. -/
theorem isCompact_factorialSeriesSweep
    (r : ∀ n, FactorialPrefix n → ℝ)
    (hr : ∀ n p, ‖r n p‖ ≤ (n + 2 : ℝ))
    (f : ℝ × Plane → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hf : ContinuousOn f (K ×ˢ factorialSeriesGraph r)) :
    IsCompact (factorialSeriesSweep r f K) :=
  (hK.prod (isCompact_factorialSeriesGraph r hr)).image_of_continuousOn
    (continuousOn_fst.prodMk hf)

theorem isCompact_factorialSeriesSweep_of_bounded
    (r : ∀ n, FactorialPrefix n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ n p, ‖r n p‖ ≤ M) (f : ℝ × Plane → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hf : ContinuousOn f (K ×ˢ factorialSeriesGraph r)) :
    IsCompact (factorialSeriesSweep r f K) :=
  (hK.prod (isCompact_factorialSeriesGraph_of_bounded r M hM hr)).image_of_continuousOn
    (continuousOn_fst.prodMk hf)

theorem mem_factorialSeriesSweep
    (r : ∀ n, FactorialPrefix n → ℝ) (f : ℝ × Plane → ℝ)
    (K : Set ℝ) (a : FactorialDigits) (t : ℝ) (ht : t ∈ K) :
    (t, f (t, (factorialValue a, factorialSelector r a))) ∈ factorialSeriesSweep r f K :=
  ⟨(t, (factorialValue a, factorialSelector r a)), ⟨ht, a, mem_univ _, rfl⟩, rfl⟩

end PlanarNikodym.Wisewell
