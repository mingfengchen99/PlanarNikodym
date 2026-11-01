import PlanarNikodym.Projection.IteratedBlindReplacement
import PlanarNikodym.Projection.ShrinkingBlindBranch

/-! Actual ancestor geometry extracted from a constructed dyadic trace.

Following the first component of every dependent child index produces
the genuine finite ancestral branch of a terminal piece. The functions
below are total on `ℕ`; all geometric claims concern the real levels
`0,...,n` of the trace.
-/

noncomputable section
open Set Metric
open scoped Topology

namespace PlanarNikodym
namespace DyadicBlindTrace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P₀ : FiniteBlindFamily E} {v : ℕ → E} {Λ : ℕ → ℝ}

/-- The actual center and half-length of the ancestor at a given level.
After the terminal level the value is held constant. -/
def branchData {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : Q.Index → ℕ → E × ℝ :=
  match trace with
  | .initial depth => fun j _ =>
      ((dyadicBlindGeneration P₀ (v 0) 1 depth).center j,
        (dyadicBlindGeneration P₀ (v 0) 1 depth).halfLength j)
  | .step previous depth _ _ _ => fun j k =>
      if k ≤ previous.level then previous.branchData j.1 k
      else
        ((dyadicBlindGeneration previous.family (v previous.level)
            (Λ previous.level) depth).center j,
          (dyadicBlindGeneration previous.family (v previous.level)
            (Λ previous.level) depth).halfLength j)

def branchCenter {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) (k : ℕ) : E :=
  (trace.branchData j k).1

def branchHalfLength {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) (k : ℕ) : ℝ :=
  (trace.branchData j k).2

theorem branchData_last {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) :
    trace.branchData j n = (Q.center j, Q.halfLength j) := by
  cases trace with
  | initial depth => rfl
  | step previous depth ε hε close =>
      simp only [branchData, level, family, Nat.not_succ_le_self, ↓reduceIte]

@[simp] theorem branchCenter_last {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) :
    trace.branchCenter j n = Q.center j := by
  rw [branchCenter, branchData_last]

@[simp] theorem branchHalfLength_last {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) :
    trace.branchHalfLength j n = Q.halfLength j := by
  rw [branchHalfLength, branchData_last]

theorem branch_center_mem_parent {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    (j : Q.Index) (k : ℕ) (hk : k < n) :
    trace.branchCenter j (k + 1) ∈
      centeredBlindSegment (trace.branchCenter j k) (v k) (trace.branchHalfLength j k) := by
  induction trace generalizing k with
  | initial depth => omega
  | @step n P previous depth ε hε close ih =>
      have hΛprev : ∀ l < n, 0 < Λ l := fun l hl =>
        hΛ l (hl.trans (Nat.lt_succ_self n))
      by_cases hkn : k = n
      · subst k
        have hp := previous.halfLength_pos hP hΛprev
        simpa only [branchCenter, branchHalfLength, branchData, level, family, dyadicBlindParent,
          Nat.not_succ_le_self, le_refl, ↓reduceIte, branchData_last] using
          dyadicBlindGeneration_center_mem_parent P (v n) (Λ n) depth
            (fun i => (hp i).le) j
      · have hlt : k < n := by omega
        have hkle : k ≤ n := hlt.le
        have hksle : k + 1 ≤ n := by omega
        simpa only [branchCenter, branchHalfLength, branchData, level, hkle, hksle,
          ↓reduceIte] using ih hΛprev j.1 k hlt

theorem branch_halfLength_shrinks {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) {β : ℝ} (hs : trace.Shrinks β)
    (j : Q.Index) (k : ℕ) (hk : k < n) :
    trace.branchHalfLength j (k + 1) ≤ β * trace.branchHalfLength j k := by
  induction trace generalizing k with
  | initial depth => omega
  | @step n P previous depth ε hε close ih =>
      obtain ⟨hprev, hcurrent⟩ := hs
      by_cases hkn : k = n
      · subst k
        simpa only [branchHalfLength, branchData, level, family,
          Nat.not_succ_le_self, le_refl, ↓reduceIte, branchData_last] using hcurrent j
      · have hlt : k < n := by omega
        have hkle : k ≤ n := hlt.le
        have hksle : k + 1 ≤ n := by omega
        simpa only [branchHalfLength, branchData, level, hkle, hksle, ↓reduceIte] using
          ih hprev j.1 k hlt

theorem branch_halfLength_pos {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    (j : Q.Index) (k : ℕ) (hk : k ≤ n) :
    0 < trace.branchHalfLength j k := by
  induction trace generalizing k with
  | initial depth =>
      have hk0 : k = 0 := by omega
      subst k
      rw [branchHalfLength_last]
      exact dyadicBlindGeneration_halfLength_pos P₀ (v 0) 1 depth hP zero_lt_one j
  | @step n P previous depth ε hε close ih =>
      have hΛprev : ∀ l < n, 0 < Λ l := fun l hl =>
        hΛ l (hl.trans (Nat.lt_succ_self n))
      by_cases hkn : k ≤ n
      · simpa only [branchHalfLength, branchData, level, hkn, ↓reduceIte] using
          ih hΛprev j.1 k hkn
      · have hkeq : k = n + 1 := by omega
        subst k
        rw [branchHalfLength_last]
        exact dyadicBlindGeneration_halfLength_pos P (v n) (Λ n) depth
          (previous.halfLength_pos hP hΛprev) (hΛ n (Nat.lt_succ_self n)) j

theorem branch_halfLength_lt {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) {ζ : ℝ} (hs : trace.AllHalfLengthLT ζ)
    (j : Q.Index) (k : ℕ) (hk : k ≤ n) :
    trace.branchHalfLength j k < ζ := by
  induction trace generalizing k with
  | initial depth =>
      have hk0 : k = 0 := by omega
      subst k
      rw [branchHalfLength_last]
      exact hs j
  | @step n P previous depth ε hε close ih =>
      obtain ⟨hprev, hcurrent⟩ := hs
      by_cases hkn : k ≤ n
      · simpa only [branchHalfLength, branchData, level, hkn, ↓reduceIte] using
          ih hprev j.1 k hkn
      · have hkeq : k = n + 1 := by omega
        subst k
        rw [branchHalfLength_last]
        exact hcurrent j

theorem branch_segment_subset_domain {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) {S : Set E} (hs : trace.InDomain S)
    (j : Q.Index) (k : ℕ) (hk : k ≤ n) :
    centeredBlindSegment (trace.branchCenter j k) (v k) (trace.branchHalfLength j k) ⊆ S := by
  induction trace generalizing k with
  | initial depth =>
      have hk0 : k = 0 := by omega
      subst k
      rw [branchCenter_last, branchHalfLength_last]
      exact fun x hx => hs (Set.mem_iUnion.mpr ⟨j, hx⟩)
  | @step n P previous depth ε hε close ih =>
      obtain ⟨hprev, hcurrent⟩ := hs
      by_cases hkn : k ≤ n
      · simpa only [branchCenter, branchHalfLength, branchData, level, hkn, ↓reduceIte] using
          ih hprev j.1 k hkn
      · have hkeq : k = n + 1 := by omega
        subst k
        rw [branchCenter_last, branchHalfLength_last]
        exact fun x hx => hcurrent (Set.mem_iUnion.mpr ⟨j, hx⟩)

/-- Every point of a terminal piece lies in the tube around each of its
actual ancestors. This supplies ancestor tubes from the constructed
trace, without assuming a separate branch or ancestor neighbourhood. -/
theorem descendant_mem_ancestor_tube {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    {β V : ℝ} (hs : trace.Shrinks β)
    (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2) (hV : 0 ≤ V)
    (hv : ∀ k ≤ n, ‖v k‖ ≤ V)
    (j : Q.Index) {y : E}
    (hy : y ∈ centeredBlindSegment (Q.center j) (v n) (Q.halfLength j))
    (k : ℕ) (hk : k ≤ n) :
    y ∈ thinSegmentTube (trace.branchCenter j k) (v k)
      (2 * trace.branchHalfLength j k) (2 * V * β * trace.branchHalfLength j k) := by
  apply shrinking_blind_descendant_mem_tube
    (trace.branchCenter j) v (trace.branchHalfLength j)
    hβ hβhalf hV
    (fun l hl => (trace.branch_halfLength_pos hP hΛ j l hl).le) hv
    (fun l hl => trace.branch_center_mem_parent hP hΛ j l hl)
    (fun l hl => trace.branch_halfLength_shrinks hs j l hl) (i := k) (hi := hk)
  simpa only [branchCenter_last, branchHalfLength_last] using hy

end DyadicBlindTrace
end PlanarNikodym
