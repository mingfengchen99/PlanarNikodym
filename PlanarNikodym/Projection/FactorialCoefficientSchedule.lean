import PlanarNikodym.Projection.FactorialDigitSeries
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Instances.Rat

/-! A bounded coefficient schedule for a local factorial selector.

For a single local family the cancellation ratios can be bounded first.
This schedule enumerates every bounded rational finite-prefix table and
extends it at a later digit position. No quantitative bound on the later
position is needed when the coefficients have a common fixed bound.
The subsequent Taylor cancellation and null-cover estimate are proved
in FactorialNullSlices. -/

noncomputable section
open Set Filter Finset
open scoped Topology Nat
namespace PlanarNikodym.Wisewell

def BoundedRationalTable (M : ℝ) (k : ℕ) :=
  {s : FactorialPrefix k → ℚ // ∀ p, |(s p : ℝ)| ≤ M}

instance (M : ℝ) (k : ℕ) : Countable (BoundedRationalTable M k) :=
  inferInstanceAs (Countable {s : FactorialPrefix k → ℚ // ∀ p, |(s p : ℝ)| ≤ M})

noncomputable instance (M : ℝ) (k : ℕ) : Encodable (BoundedRationalTable M k) :=
  Encodable.ofCountable _

abbrev AllBoundedRationalTables (M : ℝ) := Σ k : ℕ, BoundedRationalTable M k

noncomputable instance (M : ℝ) : Encodable (AllBoundedRationalTables M) :=
  Encodable.ofCountable _

def boundedCoefficientSchedule (M : ℝ) (N : ℕ) (p : FactorialPrefix N) : ℝ :=
  match Encodable.decode (α := AllBoundedRationalTables M) (Nat.unpair N).1 with
  | none => 0
  | some s => if h : s.1 ≤ N then
      (s.2.val (fun i => p ⟨i.val, lt_of_lt_of_le i.is_lt h⟩) : ℝ)
    else 0

theorem boundedCoefficientSchedule_norm_le (M : ℝ) (hM : 0 ≤ M)
    (N : ℕ) (p : FactorialPrefix N) : ‖boundedCoefficientSchedule M N p‖ ≤ M := by
  unfold boundedCoefficientSchedule
  split
  · simpa using hM
  · split_ifs
    · simpa only [Real.norm_eq_abs] using (‹AllBoundedRationalTables M›).2.property _
    · simpa using hM

/-- Every bounded rational table on `k` initial digits is copied exactly
at a coefficient position `N ≥ k`. This is an actual schedule, obtained
from natural-number pairing and decoding of rational tables. -/
theorem boundedCoefficientSchedule_extends (M : ℝ) (k : ℕ)
    (s : BoundedRationalTable M k) :
    ∃ N : ℕ, k ≤ N ∧ ∀ a : FactorialDigits,
      boundedCoefficientSchedule M N (factorialPrefix N a) =
        (s.val (factorialPrefix k a) : ℝ) := by
  let S : AllBoundedRationalTables M := ⟨k, s⟩
  let N := Nat.pair (Encodable.encode S) k
  have hkN : k ≤ N := Nat.right_le_pair _ _
  refine ⟨N, hkN, ?_⟩
  intro a
  simp only [boundedCoefficientSchedule, N, Nat.unpair_pair, Encodable.encodek, S,
    dite_true, hkN]
  rfl

theorem exists_bounded_rational_near (M x ε : ℝ) (hε : 0 < ε) (hx : |x| < M) :
    ∃ q : ℚ, |(q : ℝ)| ≤ M ∧ |x - q| < ε := by
  let δ := min ε (M - |x|)
  have hδ : 0 < δ := lt_min hε (sub_pos.mpr hx)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδM : δ ≤ M - |x| := min_le_right _ _
  obtain ⟨q, hql, hqu⟩ := exists_rat_btwn (show x - δ < x + δ by linarith)
  refine ⟨q, ?_, ?_⟩
  · apply abs_le.mpr
    constructor
    · linarith [neg_abs_le x]
    · linarith [le_abs_self x]
  · have hnear : |x - q| < δ := by
      apply abs_lt.mpr
      constructor <;> linarith
    exact hnear.trans_le hδε

/-- A cancellation table with a strict margin inside `[-M,M]` can be
approximated simultaneously on all finite prefixes. -/
theorem exists_boundedRationalTable_near (M : ℝ) (k : ℕ)
    (s : FactorialPrefix k → ℝ) (hs : ∀ p, |s p| < M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : BoundedRationalTable M k, ∀ p, |s p - q.val p| < ε := by
  choose q hq hnear using fun p => exists_bounded_rational_near M (s p) ε hε (hs p)
  exact ⟨⟨q, hq⟩, hnear⟩

/-- The schedule supplies a uniformly bounded coefficient position
approximating any prescribed cancellation table to any positive accuracy. -/
theorem boundedCoefficientSchedule_approximates (M : ℝ) (k : ℕ)
    (s : FactorialPrefix k → ℝ) (hs : ∀ p, |s p| < M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, k ≤ N ∧ ∀ a : FactorialDigits,
      |s (factorialPrefix k a) - boundedCoefficientSchedule M N (factorialPrefix N a)| < ε := by
  obtain ⟨q, hq⟩ := exists_boundedRationalTable_near M k s hs ε hε
  obtain ⟨N, hkN, hN⟩ := boundedCoefficientSchedule_extends M k q
  refine ⟨N, hkN, ?_⟩
  intro a
  rw [hN]
  exact hq _

/-- Actual cancellation of the principal affine error, uniformly on all
digit cylinders. This is the scalar main-term cancellation in Wisewell's
argument, with a bounded schedule adapted to a local slope range. -/
theorem boundedCoefficientSchedule_affine_cancellation
    (M α β : ℝ) (hβ : β ≠ 0) (hslope : |α / β| < M)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, k ≤ N ∧ ∀ a : FactorialDigits,
      |α + β * boundedCoefficientSchedule M N (factorialPrefix N a)| < ε := by
  have hδ : 0 < ε / |β| := div_pos hε (abs_pos.mpr hβ)
  obtain ⟨N, hkN, hN⟩ := boundedCoefficientSchedule_approximates M k
    (fun _ => -(α / β)) (fun _ => by simpa only [abs_neg] using hslope) (ε / |β|) hδ
  refine ⟨N, hkN, ?_⟩
  intro a
  have he : α + β * boundedCoefficientSchedule M N (factorialPrefix N a) =
      -β * (-(α / β) - boundedCoefficientSchedule M N (factorialPrefix N a)) := by
    field_simp
    ring
  rw [he, abs_mul, abs_neg]
  have hmul := mul_lt_mul_of_pos_left (hN a) (abs_pos.mpr hβ)
  have heps : |β| * (ε / |β|) = ε := by field_simp
  exact hmul.trans_eq heps

end PlanarNikodym.Wisewell
