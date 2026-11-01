import PlanarNikodym.Projection.DyadicBlindTraceGeometry
import PlanarNikodym.Projection.VenetianBlindTree

/-! Actual good-ancestor budgets for a dyadic Venetian-blind trace.

The node set and ancestor relation are read from the constructed trace.
The final length budget is proved by induction on that trace, using the
exact sum of the lengths of each parent's actual dyadic children.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace PlanarNikodym

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace DyadicBlindTrace

variable {P₀ : FiniteBlindFamily E} {v : ℕ → E} {Λ : ℕ → ℝ}

/-- The nodes actually recorded by a finite replacement trace. The first
nodes are the exact initial subdivision, before any change of direction. -/
def Node {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : Type :=
  match trace with
  | .initial _ => Q.Index
  | .step previous _ _ _ _ => previous.Node ⊕ Q.Index

instance nodeFinite {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : Finite trace.Node := by
  induction trace with
  | initial depth =>
      change Finite (dyadicBlindGeneration P₀ (v 0) 1 depth).Index
      infer_instance
  | @step n P previous depth η hη close ih =>
      letI : Finite previous.Node := ih
      change Finite (previous.Node ⊕ (dyadicBlindGeneration P (v n) (Λ n) depth).Index)
      infer_instance

instance nodeFintype {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : Fintype trace.Node := Fintype.ofFinite _

/-- Embed an actual final segment into the set of recorded nodes. -/
def terminalNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : Q.Index → trace.Node :=
  match trace with
  | .initial _ => id
  | .step _ _ _ _ _ => Sum.inr

/-- Reflexive ancestry, using the actual dyadic parent map. -/
def Descends {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : trace.Node → Q.Index → Prop :=
  match trace with
  | .initial _ => fun i j => i = j
  | .step previous _ _ _ _ => fun u j =>
      match u with
      | .inl a => previous.Descends a j.1
      | .inr i => i = j

def nodeHalfLength {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : trace.Node → ℝ :=
  match trace with
  | .initial depth => (dyadicBlindGeneration P₀ (v 0) 1 depth).halfLength
  | .step previous depth _ _ _ => Sum.elim previous.nodeHalfLength
      (dyadicBlindGeneration previous.family (v previous.level) (Λ previous.level) depth).halfLength

/-- Center and level of an actual recorded node. -/
def nodeCenter {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : trace.Node → E :=
  match trace with
  | .initial depth => (dyadicBlindGeneration P₀ (v 0) 1 depth).center
  | .step previous depth _ _ _ => Sum.elim previous.nodeCenter
      (dyadicBlindGeneration previous.family (v previous.level) (Λ previous.level) depth).center

def nodeLevel {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : trace.Node → ℕ :=
  match trace with
  | .initial _ => fun _ => 0
  | .step previous _ _ _ _ => Sum.elim previous.nodeLevel (fun _ => previous.level + 1)

/-- Follow the real dyadic parent maps to the requested ancestor level.
For indices beyond the last level this returns the terminal node. -/
def ancestorNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) : Q.Index → ℕ → trace.Node :=
  match trace with
  | .initial _ => fun j _ => j
  | .step previous _ _ _ _ => fun j k =>
      if k ≤ previous.level then .inl (previous.ancestorNode j.1 k) else .inr j

theorem nodeLevel_le {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (u : trace.Node) : trace.nodeLevel u ≤ n := by
  induction trace with
  | initial depth => exact le_rfl
  | @step n P previous depth η hη close ih =>
      cases u with
      | inl u => exact (ih u).trans (Nat.le_succ n)
      | inr j => exact le_rfl

theorem descends_ancestorNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) (k : ℕ) :
    trace.Descends (trace.ancestorNode j k) j := by
  induction trace with
  | initial depth => exact rfl
  | @step n P previous depth η hη close ih =>
      by_cases hk : k ≤ n
      · simpa only [ancestorNode, level, hk, ↓reduceIte, Descends] using ih j.1
      · simp only [ancestorNode, level, hk, ↓reduceIte, Descends]

theorem nodeLevel_ancestorNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) (k : ℕ) (hk : k ≤ n) :
    trace.nodeLevel (trace.ancestorNode j k) = k := by
  induction trace with
  | initial depth =>
      have : k = 0 := by omega
      subst k
      rfl
  | @step n P previous depth η hη close ih =>
      by_cases hkn : k ≤ n
      · simpa only [ancestorNode, level, hkn, ↓reduceIte, nodeLevel, Sum.elim_inl] using ih j.1 hkn
      · have : k = n + 1 := by omega
        subst k
        simp only [ancestorNode, level, Nat.not_succ_le_self, ↓reduceIte, nodeLevel, Sum.elim_inr]

theorem nodeCenter_ancestorNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) (k : ℕ) :
    trace.nodeCenter (trace.ancestorNode j k) = trace.branchCenter j k := by
  induction trace with
  | initial depth => rfl
  | @step n P previous depth η hη close ih =>
      by_cases hk : k ≤ n
      · simpa only [ancestorNode, level, hk, ↓reduceIte, nodeCenter, Sum.elim_inl,
          branchCenter, branchData] using ih j.1
      · simp only [ancestorNode, level, hk, ↓reduceIte, nodeCenter, Sum.elim_inr,
          branchCenter, branchData, family]

theorem nodeHalfLength_ancestorNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (j : Q.Index) (k : ℕ) :
    trace.nodeHalfLength (trace.ancestorNode j k) = trace.branchHalfLength j k := by
  induction trace with
  | initial depth => rfl
  | @step n P previous depth η hη close ih =>
      by_cases hk : k ≤ n
      · simpa only [ancestorNode, level, hk, ↓reduceIte, nodeHalfLength, Sum.elim_inl,
          branchHalfLength, branchData] using ih j.1
      · simp only [ancestorNode, level, hk, ↓reduceIte, nodeHalfLength, Sum.elim_inr,
          branchHalfLength, branchData, family]

/-- An actual ancestor is exactly the node obtained by following parent
indices back to its recorded level. -/
theorem eq_ancestorNode_of_descends {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (u : trace.Node) (j : Q.Index)
    (hu : trace.Descends u j) : u = trace.ancestorNode j (trace.nodeLevel u) := by
  induction trace with
  | initial depth => exact hu
  | @step n P previous depth η hη close ih =>
      cases u with
      | inl u =>
          have hlevel := previous.nodeLevel_le u
          change Sum.inl u = (if previous.nodeLevel u ≤ n then
            Sum.inl (previous.ancestorNode j.1 (previous.nodeLevel u)) else Sum.inr j)
          rw [if_pos hlevel]
          exact congrArg Sum.inl (ih u j.1 hu)
      | inr i =>
          have hie : i = j := hu
          subst i
          simp only [nodeLevel, Sum.elim_inr, level, ancestorNode, Nat.not_succ_le_self, ↓reduceIte]

/-- Every descendant gives the same center and length when followed back
to this recorded ancestor's level. -/
theorem branchData_of_descends {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (u : trace.Node) (j : Q.Index)
    (hu : trace.Descends u j) :
    trace.branchData j (trace.nodeLevel u) = (trace.nodeCenter u, trace.nodeHalfLength u) := by
  apply Prod.ext
  · change trace.branchCenter j (trace.nodeLevel u) = trace.nodeCenter u
    conv_rhs => rw [trace.eq_ancestorNode_of_descends u j hu]
    exact (trace.nodeCenter_ancestorNode j _).symm
  · change trace.branchHalfLength j (trace.nodeLevel u) = trace.nodeHalfLength u
    conv_rhs => rw [trace.eq_ancestorNode_of_descends u j hu]
    exact (trace.nodeHalfLength_ancestorNode j _).symm

/-- The union of the specified terminal sets below a recorded node. -/
def descendantUnion {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (C : Q.Index → Set ℝ) :
    trace.Node → Set ℝ :=
  match trace with
  | .initial _ => C
  | .step previous depth _ _ _ => Sum.elim
      (previous.descendantUnion fun i =>
        ⋃ j : ↥(dyadicBlindCenters (previous.family.center i)
          (v previous.level) (previous.family.halfLength i) (depth i)), C ⟨i, j⟩) C

@[simp] theorem descends_terminalNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (i j : Q.Index) :
    trace.Descends (trace.terminalNode i) j ↔ i = j := by
  cases trace <;> rfl

@[simp] theorem nodeHalfLength_terminalNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (i : Q.Index) :
    trace.nodeHalfLength (trace.terminalNode i) = Q.halfLength i := by
  cases trace <;> rfl

@[simp] theorem descendantUnion_terminalNode {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (C : Q.Index → Set ℝ) (i : Q.Index) :
    trace.descendantUnion C (trace.terminalNode i) = C i := by
  cases trace <;> rfl

theorem mem_descendantUnion_iff {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (C : Q.Index → Set ℝ)
    (u : trace.Node) (x : ℝ) :
    x ∈ trace.descendantUnion C u ↔ ∃ j, trace.Descends u j ∧ x ∈ C j := by
  induction trace with
  | initial depth => simp [descendantUnion, Descends]
  | @step n P previous depth ε hε close ih =>
      cases u with
      | inl u =>
          simp only [descendantUnion, Sum.elim_inl, ih, Descends]
          simp only [mem_iUnion]
          constructor
          · rintro ⟨i, hi, j, hj⟩
            exact ⟨⟨i, j⟩, hi, hj⟩
          · rintro ⟨⟨i, j⟩, hi, hj⟩
            exact ⟨i, hi, j, hj⟩
      | inr j => simp [descendantUnion, Descends]

/-- The actual recorded nodes have positive lengths. -/
theorem nodeHalfLength_pos {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    (u : trace.Node) : 0 < trace.nodeHalfLength u := by
  induction trace with
  | initial depth => exact dyadicBlindGeneration_halfLength_pos _ _ _ _ hP zero_lt_one u
  | @step n P previous depth ε hε close ih =>
      cases u with
      | inl u => exact ih (fun k hk => hΛ k (hk.trans (Nat.lt_succ_self n))) u
      | inr j =>
          exact dyadicBlindGeneration_halfLength_pos P (v n) (Λ n) depth
            (previous.halfLength_pos hP (fun k hk => hΛ k (hk.trans (Nat.lt_succ_self n))))
            (hΛ n (Nat.lt_succ_self n)) j

end DyadicBlindTrace

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Converting an actual finite segment family's real length budget to
extended nonnegative length does not lose mass when all lengths are nonnegative. -/
theorem sum_ofReal_twice_halfLength (P : FiniteBlindFamily E)
    (hP : ∀ i, 0 ≤ P.halfLength i) :
    (∑ i, ENNReal.ofReal (2 * P.halfLength i)) = ENNReal.ofReal (2 * P.budget) := by
  rw [FiniteBlindFamily.budget, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by norm_num) (hP i))]

/-- The exact dyadic child-length identity in the measure-valued form
needed for good-ancestor projection estimates. -/
theorem dyadicBlindGeneration_parent_ofReal_length
    (P : FiniteBlindFamily E) (v : E) (Λ : ℝ) (depth : P.Index → ℕ)
    (hP : ∀ i, 0 < P.halfLength i) (hv : v ≠ 0) (hΛ : 0 ≤ Λ) (i : P.Index) :
    (∑ z : ↥(dyadicBlindCenters (P.center i) v (P.halfLength i) (depth i)),
      ENNReal.ofReal (2 * (dyadicBlindGeneration P v Λ depth).halfLength ⟨i, z⟩)) =
      ENNReal.ofReal Λ * ENNReal.ofReal (2 * P.halfLength i) := by
  have hchild : ∀ z : ↥(dyadicBlindCenters (P.center i) v (P.halfLength i) (depth i)),
      0 ≤ 2 * (dyadicBlindGeneration P v Λ depth).halfLength ⟨i, z⟩ := by
    intro z
    exact mul_nonneg (by norm_num) (mul_nonneg hΛ (div_nonneg (hP i).le (by positivity)))
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hchild z), ← Finset.mul_sum,
    dyadicBlindGeneration_parent_budget P v Λ depth hP hv i]
  rw [show 2 * (Λ * P.halfLength i) = Λ * (2 * P.halfLength i) by ring,
    ENNReal.ofReal_mul hΛ]

namespace DyadicBlindTrace

variable {P₀ : FiniteBlindFamily E} {v : ℕ → E} {Λ : ℕ → ℝ}

/-- Every leaf of the actual trace has a marked ancestor. -/
def EveryBranchMarked {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (good : trace.Node → Prop) : Prop :=
  ∀ j, ∃ u, trace.Descends u j ∧ good u

/-- Finite good-ancestor measure estimate for the *actual* dyadic trace.
The local weight inequalities are consequences of exact dyadic child
lengths and `1 ≤ Λ`; neither a tree budget nor a cut budget is assumed. -/
theorem volume_terminalUnion_le {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i)
    (hΛ : ∀ k < n, 1 ≤ Λ k) (hv : ∀ k < n, v k ≠ 0)
    (ε : ℝ≥0∞) (good : trace.Node → Prop) (C : Q.Index → Set ℝ)
    (hgood : ∀ u, good u → volume (trace.descendantUnion C u) ≤
      ε * ENNReal.ofReal (2 * trace.nodeHalfLength u))
    (hbranch : trace.EveryBranchMarked good) :
    volume (⋃ j, C j) ≤ ε * ENNReal.ofReal (2 * Q.budget) := by
  classical
  induction trace generalizing ε with
  | initial depth =>
      have hlength := dyadicBlindGeneration_halfLength_pos P₀ (v 0) 1 depth hP₀ zero_lt_one
      calc
        volume (⋃ j, C j) ≤ ∑ j, volume (C j) := measure_iUnion_fintype_le volume C
        _ ≤ ∑ j, ε * ENNReal.ofReal (2 *
            (dyadicBlindGeneration P₀ (v 0) 1 depth).halfLength j) := by
          apply Finset.sum_le_sum
          intro j _
          obtain ⟨u, hu, hgu⟩ := hbranch j
          have hue : u = j := hu
          subst u
          exact hgood j hgu
        _ = ε * ENNReal.ofReal (2 * (dyadicBlindGeneration P₀ (v 0) 1 depth).budget) := by
          rw [← Finset.mul_sum, sum_ofReal_twice_halfLength _ (fun j => (hlength j).le)]
  | @step n P previous depth η hη close ih =>
      let Child (i : P.Index) := ↥(dyadicBlindCenters (P.center i) (v n) (P.halfLength i) (depth i))
      let C' : P.Index → Set ℝ := fun i => ⋃ z : Child i, C ⟨i, z⟩
      let good' : previous.Node → Prop := fun u => good (Sum.inl u) ∨
        ∃ i, previous.terminalNode i = u ∧ ∀ z : Child i, good (Sum.inr ⟨i, z⟩)
      have hΛn : 1 ≤ Λ n := hΛ n (Nat.lt_succ_self n)
      have hΛn0 : 0 ≤ Λ n := le_trans zero_le_one hΛn
      have hΛ' : ∀ k < n, 1 ≤ Λ k := fun k hk => hΛ k (hk.trans (Nat.lt_succ_self n))
      have hv' : ∀ k < n, v k ≠ 0 := fun k hk => hv k (hk.trans (Nat.lt_succ_self n))
      have hP : ∀ i, 0 < P.halfLength i := previous.halfLength_pos hP₀
        (fun k hk => lt_of_lt_of_le zero_lt_one (hΛ' k hk))
      have hfactor : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Λ n) := by
        simpa using ENNReal.ofReal_le_ofReal hΛn
      have hbranch' : previous.EveryBranchMarked good' := by
        intro i
        by_cases hi : ∃ u, previous.Descends u i ∧ good (Sum.inl u)
        · obtain ⟨u, hu, hgu⟩ := hi
          exact ⟨u, hu, Or.inl hgu⟩
        · refine ⟨previous.terminalNode i, (previous.descends_terminalNode i i).mpr rfl,
            Or.inr ⟨i, rfl, ?_⟩⟩
          intro z
          obtain ⟨u, hu, hgu⟩ := hbranch ⟨i, z⟩
          cases u with
          | inl a => exact False.elim (hi ⟨a, hu, hgu⟩)
          | inr j =>
              have hje : j = ⟨i, z⟩ := hu
              subst j
              exact hgu
      have hgood' : ∀ u, good' u → volume (previous.descendantUnion C' u) ≤
          (ε * ENNReal.ofReal (Λ n)) * ENNReal.ofReal (2 * previous.nodeHalfLength u) := by
        intro u hu
        rcases hu with hu | ⟨i, rfl, hi⟩
        · calc
            volume (previous.descendantUnion C' u) ≤
                ε * ENNReal.ofReal (2 * previous.nodeHalfLength u) := hgood (Sum.inl u) hu
            _ ≤ (ε * ENNReal.ofReal (Λ n)) * ENNReal.ofReal (2 * previous.nodeHalfLength u) := by
              calc
                _ = (ε * 1) * ENNReal.ofReal (2 * previous.nodeHalfLength u) := by simp
                _ ≤ _ := mul_le_mul_left (mul_le_mul_right hfactor ε) _
        · rw [previous.descendantUnion_terminalNode, previous.nodeHalfLength_terminalNode]
          calc
            volume (C' i) ≤ ∑ z : Child i, volume (C ⟨i, z⟩) :=
              measure_iUnion_fintype_le volume _
            _ ≤ ∑ z : Child i, ε * ENNReal.ofReal
                (2 * (dyadicBlindGeneration P (v n) (Λ n) depth).halfLength ⟨i, z⟩) := by
              apply Finset.sum_le_sum
              intro z _
              exact hgood (Sum.inr ⟨i, z⟩) (hi z)
            _ = (ε * ENNReal.ofReal (Λ n)) * ENNReal.ofReal (2 * P.halfLength i) := by
              rw [← Finset.mul_sum, dyadicBlindGeneration_parent_ofReal_length P (v n)
                (Λ n) depth hP (hv n (Nat.lt_succ_self n)) hΛn0 i]
              exact (mul_assoc _ _ _).symm
      have hind := ih hΛ' hv' (ε * ENNReal.ofReal (Λ n)) good' C' hgood' hbranch'
      have hunion : (⋃ i, C' i) = ⋃ j, C j := by
        ext x
        simp only [C', mem_iUnion]
        constructor
        · rintro ⟨i, z, hz⟩
          exact ⟨⟨i, z⟩, hz⟩
        · rintro ⟨⟨i, z⟩, hz⟩
          exact ⟨i, z, hz⟩
      rw [hunion] at hind
      convert hind using 1
      rw [dyadicBlindGeneration_budget_eq P (v n) (Λ n) depth hP
        (hv n (Nat.lt_succ_self n))]
      rw [show 2 * (Λ n * P.budget) = Λ n * (2 * P.budget) by ring,
        ENNReal.ofReal_mul hΛn0, mul_assoc]

/-- Check the branch condition by supplying a good level on each actual
ancestral branch, as produced by the slope-grid compression argument. -/
theorem everyBranchMarked_of_ancestor {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (good : trace.Node → Prop)
    (hgood : ∀ j, ∃ k ≤ n, good (trace.ancestorNode j k)) :
    trace.EveryBranchMarked good := by
  intro j
  obtain ⟨k, _, hk⟩ := hgood j
  exact ⟨trace.ancestorNode j k, trace.descends_ancestorNode j k, hk⟩

/-- The generic terminal-set budget applied to genuine projected final
segments. A good-node cover is only an analytic estimate on that node's
descendants; the global length budget is proved from the trace. -/
theorem volume_projected_carrier_le {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i)
    (hΛ : ∀ k < n, 1 ≤ Λ k) (hv : ∀ k < n, v k ≠ 0)
    (f : E → ℝ) (ε : ℝ≥0∞) (good : trace.Node → Prop)
    (A : trace.Node → Set ℝ)
    (hcover : ∀ u, good u → ∀ j, trace.Descends u j →
      f '' centeredBlindSegment (Q.center j) (v n) (Q.halfLength j) ⊆ A u)
    (hmeasure : ∀ u, good u → volume (A u) ≤
      ε * ENNReal.ofReal (2 * trace.nodeHalfLength u))
    (hbranch : trace.EveryBranchMarked good) :
    volume (f '' Q.carrier (v n)) ≤ ε * ENNReal.ofReal (2 * Q.budget) := by
  rw [FiniteBlindFamily.carrier, image_iUnion]
  apply trace.volume_terminalUnion_le hP₀ hΛ hv ε good _ _ hbranch
  intro u hu
  apply le_trans (measure_mono ?_) (hmeasure u hu)
  intro x hx
  obtain ⟨j, hju, hxj⟩ := (trace.mem_descendantUnion_iff _ u x).mp hx
  exact hcover u hu j hju hxj

/-- The geometrically proved relative tube around an actual node. -/
def nodeTube {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (β V : ℝ) (u : trace.Node) : Set E :=
  thinSegmentTube (trace.nodeCenter u) (v (trace.nodeLevel u))
    (2 * trace.nodeHalfLength u) (2 * V * β * trace.nodeHalfLength u)

/-- Every real descendant lies in its actual ancestor tube. This combines
the parent-index relation with the geometric shrinking-branch theorem. -/
theorem terminalSegment_subset_nodeTube {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    {β V : ℝ} (hs : trace.Shrinks β) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (hV : 0 ≤ V) (hv : ∀ k ≤ n, ‖v k‖ ≤ V)
    (u : trace.Node) (j : Q.Index) (huj : trace.Descends u j) :
    centeredBlindSegment (Q.center j) (v n) (Q.halfLength j) ⊆ trace.nodeTube β V u := by
  intro y hy
  have hk := trace.nodeLevel_le u
  have h := trace.descendant_mem_ancestor_tube hP₀ hΛ hs hβ hβhalf hV hv j hy
    (trace.nodeLevel u) hk
  have hc : trace.nodeCenter u = trace.branchCenter j (trace.nodeLevel u) := by
    conv_lhs => rw [trace.eq_ancestorNode_of_descends u j huj]
    exact trace.nodeCenter_ancestorNode j _
  have ha : trace.nodeHalfLength u = trace.branchHalfLength j (trace.nodeLevel u) := by
    conv_lhs => rw [trace.eq_ancestorNode_of_descends u j huj]
    exact trace.nodeHalfLength_ancestorNode j _
  simpa only [nodeTube, hc, ha] using h

/-- Complete finite trace assembly: good-ancestor tube projection bounds
imply the small projection estimate for the genuine final segment union.
All ancestor containments and all finite length budgets are proved here
from the constructed trace, rather than supplied as global hypotheses. -/
theorem volume_projected_carrier_le_of_good_tubes {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i)
    (hΛ : ∀ k < n, 1 ≤ Λ k) (hvne : ∀ k < n, v k ≠ 0)
    {β V : ℝ} (hs : trace.Shrinks β) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (hV : 0 ≤ V) (hv : ∀ k ≤ n, ‖v k‖ ≤ V)
    (f : E → ℝ) (ε : ℝ≥0∞) (good : trace.Node → Prop)
    (hmeasure : ∀ u, good u → volume (f '' trace.nodeTube β V u) ≤
      ε * ENNReal.ofReal (2 * trace.nodeHalfLength u))
    (hbranch : trace.EveryBranchMarked good) :
    volume (f '' Q.carrier (v n)) ≤ ε * ENNReal.ofReal (2 * Q.budget) := by
  apply trace.volume_projected_carrier_le hP₀ hΛ hvne f ε good
    (fun u => f '' trace.nodeTube β V u) _ hmeasure hbranch
  intro u _ j hju
  exact image_mono (trace.terminalSegment_subset_nodeTube hP₀
    (fun k hk => lt_of_lt_of_le zero_lt_one (hΛ k hk)) hs hβ hβhalf hV hv u j hju)

/-- A single positive radius fits the relative length margin at every
recorded node. The empty finite family is allowed. -/
theorem exists_uniform_node_radius {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP₀ : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ ρ > 0, ∀ u : trace.Node, ρ < γ * trace.nodeHalfLength u := by
  classical
  have hfinite : ∀ s : Finset trace.Node,
      ∃ ρ > 0, ∀ u ∈ s, ρ < γ * trace.nodeHalfLength u := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert u s hu ih =>
        obtain ⟨ρ, hρ, hs⟩ := ih
        have hprod : 0 < γ * trace.nodeHalfLength u :=
          mul_pos hγ (trace.nodeHalfLength_pos hP₀ hΛ u)
        refine ⟨min ρ (γ * trace.nodeHalfLength u / 2),
          lt_min hρ (half_pos hprod), ?_⟩
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact (min_le_right _ _).trans_lt (half_lt_self hprod)
        · exact (min_le_left _ _).trans_lt (hs a ha)
  obtain ⟨ρ, hρ, hall⟩ := hfinite Finset.univ
  exact ⟨ρ, hρ, fun u => hall u (Finset.mem_univ u)⟩

/-- Equivalent finite-level form of the real good-ancestor condition. -/
theorem everyBranchMarked_iff_ancestor {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (good : trace.Node → Prop) :
    trace.EveryBranchMarked good ↔ ∀ j, ∃ k ≤ n, good (trace.ancestorNode j k) := by
  constructor
  · intro h j
    obtain ⟨u, hu, hgu⟩ := h j
    refine ⟨trace.nodeLevel u, trace.nodeLevel_le u, ?_⟩
    rwa [← trace.eq_ancestorNode_of_descends u j hu]
  · exact trace.everyBranchMarked_of_ancestor good

end DyadicBlindTrace

end PlanarNikodym
