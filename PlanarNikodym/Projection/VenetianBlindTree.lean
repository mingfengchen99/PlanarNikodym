import PlanarNikodym.Projection.ProjectedSweepTransfer

/-! Finite good-ancestor budgets for iterated Venetian blinds.

Each leaf represents a final segment. At an internal node, its length
is at most the total length of its children. The first good nodes along
the branches form an actual finite antichain. Their total length is at
most the final leaf length, which gives the projection measure budget.
The geometric estimates deciding which nodes are good remain separate.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace PlanarNikodym

/-- A finite tree with finite branching, segment lengths and good-node
markers. Different nodes are distinguished by their branch paths. -/
inductive VenetianBlindTree where
  | leaf (length : ℝ≥0∞) (good : Bool)
  | split (length : ℝ≥0∞) (good : Bool) (arity : ℕ)
      (children : Fin arity → VenetianBlindTree)

namespace VenetianBlindTree

abbrev WeightedPath := List ℕ × ℝ≥0∞

def prepend (i : ℕ) : WeightedPath ↪ WeightedPath where
  toFun p := (i :: p.1, p.2)
  inj' := by
    rintro ⟨p, w⟩ ⟨q, v⟩ h
    simpa using h

def branchUnion {n : ℕ} (s : Fin n → Finset WeightedPath) : Finset WeightedPath := by
  classical
  exact Finset.univ.biUnion fun i => (s i).map (prepend i.val)

theorem mem_branchUnion {n : ℕ} (s : Fin n → Finset WeightedPath)
    (p : WeightedPath) :
    p ∈ branchUnion s ↔ ∃ i q, q ∈ s i ∧ prepend i.val q = p := by
  simp [branchUnion]

theorem sum_length_branchUnion {n : ℕ} (s : Fin n → Finset WeightedPath) :
    ∑ p ∈ branchUnion s, p.2 = ∑ i, ∑ p ∈ s i, p.2 := by
  rw [branchUnion, Finset.sum_biUnion]
  · simp only [Finset.sum_map, prepend, Function.Embedding.coeFn_mk]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hpi
    obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hpj
    have he := ha.trans hb.symm
    have hv : i.val = j.val := by
      have hlist : i.val :: a.1 = j.val :: b.1 := congrArg Prod.fst he
      exact (List.cons.inj hlist).1
    exact hij (Fin.ext hv)

def rootLength : VenetianBlindTree → ℝ≥0∞
  | .leaf w _ => w
  | .split w _ _ _ => w

def leafLength : VenetianBlindTree → ℝ≥0∞
  | .leaf w _ => w
  | .split _ _ _ children => ∑ i, leafLength (children i)

/-- The local length inequality is required only at immediate splits. -/
def LengthExpanding : VenetianBlindTree → Prop
  | .leaf _ _ => True
  | .split w _ _ children =>
      w ≤ ∑ i, rootLength (children i) ∧ ∀ i, LengthExpanding (children i)

/-- Every root-to-leaf branch meets a good node. -/
def GoodOnEveryBranch : VenetianBlindTree → Prop
  | .leaf _ good => good = true
  | .split _ good _ children => good = true ∨ ∀ i, GoodOnEveryBranch (children i)

/-- The first good nodes; descent stops immediately at a good node. -/
def firstGood : VenetianBlindTree → Finset WeightedPath
  | .leaf w good => if good then {([], w)} else ∅
  | .split w good _ children =>
      if good then {([], w)} else branchUnion fun i => firstGood (children i)

/-- All terminal segments, with their full paths from the root. -/
def leaves : VenetianBlindTree → Finset WeightedPath
  | .leaf w _ => {([], w)}
  | .split _ _ _ children => branchUnion fun i => leaves (children i)

/-- Read the actual marker at a path; nonexistent paths have no good
marker. -/
def goodAt : VenetianBlindTree → List ℕ → Bool
  | .leaf _ good, [] => good
  | .leaf _ _, _ :: _ => false
  | .split _ good _ _, [] => good
  | .split _ _ n children, i :: path =>
      if hi : i < n then goodAt (children ⟨i, hi⟩) path else false

theorem firstGood_marked (T : VenetianBlindTree) :
    ∀ a ∈ T.firstGood, T.goodAt a.1 = true := by
  induction T with
  | leaf w good =>
    cases good <;> simp [firstGood, goodAt]
  | split w good n children ih =>
    cases good with
    | true => simp [firstGood, goodAt]
    | false =>
      intro a ha
      obtain ⟨i, a', ha', rfl⟩ := (mem_branchUnion _ a).mp ha
      simpa only [prepend, Function.Embedding.coeFn_mk, goodAt, i.isLt, ↓reduceDIte] using
        ih i a' ha'

/-- A selected good node has no earlier good ancestor. -/
theorem firstGood_minimal (T : VenetianBlindTree) :
    ∀ a ∈ T.firstGood, ∀ path, path <+: a.1 →
      T.goodAt path = true → path = a.1 := by
  induction T with
  | leaf w good =>
    cases good with
    | false => simp [firstGood]
    | true =>
      intro a ha path hp hg
      have ha' : a = ([], w) := by simpa only [firstGood, ↓reduceIte, Finset.mem_singleton] using ha
      subst a
      exact List.eq_nil_of_prefix_nil hp
  | split w good n children ih =>
    cases good with
    | true =>
      intro a ha path hp hg
      have ha' : a = ([], w) := by simpa only [firstGood, ↓reduceIte, Finset.mem_singleton] using ha
      subst a
      exact List.eq_nil_of_prefix_nil hp
    | false =>
      intro a ha path hp hg
      obtain ⟨i, a', ha', rfl⟩ := (mem_branchUnion _ a).mp ha
      cases path with
      | nil => simp only [goodAt, Bool.false_eq_true] at hg
      | cons j path =>
        obtain ⟨hji, hpath⟩ := List.cons_prefix_cons.mp hp
        subst j
        have hgood : (children i).goodAt path = true := by
          simpa only [goodAt, i.isLt, ↓reduceDIte] using hg
        exact congrArg (List.cons i.val) (ih i a' ha' path hpath hgood)

theorem sum_length_leaves (T : VenetianBlindTree) :
    ∑ p ∈ T.leaves, p.2 = T.leafLength := by
  induction T with
  | leaf w good => simp [leaves, leafLength]
  | split w good n children ih =>
    simp only [leaves, sum_length_branchUnion, leafLength, ih]

/-- The total final length dominates each original root length, derived
by finite tree induction from the immediate-child inequalities. -/
theorem rootLength_le_leafLength (T : VenetianBlindTree) (h : T.LengthExpanding) :
    T.rootLength ≤ T.leafLength := by
  induction T with
  | leaf w good => exact le_rfl
  | split w good n children ih =>
    exact h.1.trans (Finset.sum_le_sum fun i _ => ih i (h.2 i))

/-- The first-good antichain length budget follows from local length
expansion. It is not an additional assumption on the selected nodes. -/
theorem sum_length_firstGood_le_leafLength
    (T : VenetianBlindTree) (h : T.LengthExpanding) :
    ∑ p ∈ T.firstGood, p.2 ≤ T.leafLength := by
  induction T with
  | leaf w good =>
    cases good <;> simp [firstGood, leafLength]
  | split w good n children ih =>
    cases good with
    | false =>
      simp only [firstGood, Bool.false_eq_true, ↓reduceIte, sum_length_branchUnion,
        leafLength]
      exact Finset.sum_le_sum fun i _ => ih i (h.2 i)
    | true =>
      simpa only [firstGood, ↓reduceIte, Finset.sum_singleton, rootLength] using
        rootLength_le_leafLength (.split w true n children) h

/-- No two selected first-good nodes stand in a proper ancestor
relation. The equality includes their stored lengths. -/
theorem firstGood_antichain (T : VenetianBlindTree) :
    ∀ a ∈ T.firstGood, ∀ b ∈ T.firstGood, a.1 <+: b.1 → a = b := by
  induction T with
  | leaf w good =>
    cases good <;> simp [firstGood]
  | split w good n children ih =>
    cases good with
    | true => simp [firstGood]
    | false =>
      intro a ha b hb hab
      obtain ⟨i, a', ha', rfl⟩ := (mem_branchUnion _ a).mp ha
      obtain ⟨j, b', hb', rfl⟩ := (mem_branchUnion _ b).mp hb
      obtain ⟨hij, hprefix⟩ := List.cons_prefix_cons.mp hab
      have he : i = j := Fin.ext hij
      subst j
      exact congrArg (prepend i.val) (ih i a' ha' b' hb' hprefix)

/-- Every leaf has an ancestor in the first-good antichain if each
branch contains a good node. -/
theorem firstGood_covers_leaves (T : VenetianBlindTree) (h : T.GoodOnEveryBranch) :
    ∀ b ∈ T.leaves, ∃ a ∈ T.firstGood, a.1 <+: b.1 := by
  induction T with
  | leaf w good =>
    have hg : good = true := h
    subst good
    intro b hb
    exact ⟨([], w), by simp [firstGood], List.nil_prefix⟩
  | split w good n children ih =>
    cases good with
    | true =>
      intro b hb
      exact ⟨([], w), by simp [firstGood], List.nil_prefix⟩
    | false =>
      have hc : ∀ i, GoodOnEveryBranch (children i) := by
        simpa only [GoodOnEveryBranch, Bool.false_eq_true, false_or] using h
      intro b hb
      obtain ⟨i, b', hb', rfl⟩ := (mem_branchUnion _ b).mp hb
      obtain ⟨a, ha, hab⟩ := ih i (hc i) b' hb'
      refine ⟨prepend i.val a, ?_, List.cons_prefix_cons.mpr ⟨rfl, hab⟩⟩
      exact (mem_branchUnion _ _).mpr ⟨i, a, ha, rfl⟩

/-- The recursive branch condition is equivalent to the geometric form:
each final leaf has some ancestor whose actual marker is good. -/
theorem goodOnEveryBranch_iff_marked_ancestor (T : VenetianBlindTree) :
    T.GoodOnEveryBranch ↔
      ∀ b ∈ T.leaves, ∃ path, path <+: b.1 ∧ T.goodAt path = true := by
  constructor
  · intro h b hb
    obtain ⟨a, ha, hab⟩ := T.firstGood_covers_leaves h b hb
    exact ⟨a.1, hab, T.firstGood_marked a ha⟩
  · intro h
    induction T with
    | leaf w good =>
      obtain ⟨path, hp, hg⟩ := h ([], w) (by simp [leaves])
      have he : path = [] := List.eq_nil_of_prefix_nil hp
      simpa only [he, goodAt, GoodOnEveryBranch] using hg
    | split w good n children ih =>
      cases good with
      | true => exact Or.inl rfl
      | false =>
        apply Or.inr
        intro i
        apply ih i
        intro b hb
        have hparent : prepend i.val b ∈ (.split w false n children : VenetianBlindTree).leaves :=
          (mem_branchUnion _ _).mpr ⟨i, b, hb, rfl⟩
        obtain ⟨path, hp, hg⟩ := h (prepend i.val b) hparent
        cases path with
        | nil => simp only [goodAt, Bool.false_eq_true] at hg
        | cons j path =>
          obtain ⟨hji, hpath⟩ := List.cons_prefix_cons.mp hp
          subst j
          refine ⟨path, hpath, ?_⟩
          simpa only [goodAt, i.isLt, ↓reduceDIte] using hg

/-- Good-ancestor coverage gives a cover of the actual leaf sets.
The ancestor sets may be tubes around ancestor segments rather than
the segments themselves. -/
theorem leafUnion_subset_firstGoodUnion {α : Type*}
    (T : VenetianBlindTree) (h : T.GoodOnEveryBranch)
    (leafSet goodSet : List ℕ → Set α)
    (hcover : ∀ a ∈ T.firstGood, ∀ b ∈ T.leaves, a.1 <+: b.1 →
      leafSet b.1 ⊆ goodSet a.1) :
    (⋃ b ∈ T.leaves, leafSet b.1) ⊆ ⋃ a ∈ T.firstGood, goodSet a.1 := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := mem_iUnion.mp hx |>.imp fun b => mem_iUnion.mp
  obtain ⟨a, ha, hab⟩ := T.firstGood_covers_leaves h b hb
  exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, hcover a ha b hb hab hxb⟩⟩

/-- The small-projection estimates on first-good nodes imply a bound
by the entire final leaf length, with no measurability requirement on
the projected sets. -/
theorem measure_firstGoodUnion_le {α : Type*} [MeasurableSpace α]
    (T : VenetianBlindTree) (h : T.LengthExpanding)
    (μ : Measure α) (S : List ℕ → Set α) (ε : ℝ≥0∞)
    (hgood : ∀ a ∈ T.firstGood, μ (S a.1) ≤ ε * a.2) :
    μ (⋃ a ∈ T.firstGood, S a.1) ≤ ε * T.leafLength := by
  calc
    μ (⋃ a ∈ T.firstGood, S a.1) ≤ ∑ a ∈ T.firstGood, μ (S a.1) :=
      measure_biUnion_finset_le T.firstGood _
    _ ≤ ∑ a ∈ T.firstGood, ε * a.2 := Finset.sum_le_sum hgood
    _ = ε * ∑ a ∈ T.firstGood, a.2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ε * T.leafLength := mul_le_mul' le_rfl (T.sum_length_firstGood_le_leafLength h)

theorem measure_leafUnion_le {α : Type*} [MeasurableSpace α]
    (T : VenetianBlindTree) (h : T.LengthExpanding) (hg : T.GoodOnEveryBranch)
    (μ : Measure α) (leafSet goodSet : List ℕ → Set α) (ε : ℝ≥0∞)
    (hcover : ∀ a ∈ T.firstGood, ∀ b ∈ T.leaves, a.1 <+: b.1 →
      leafSet b.1 ⊆ goodSet a.1)
    (hgood : ∀ a ∈ T.firstGood, μ (goodSet a.1) ≤ ε * a.2) :
    μ (⋃ b ∈ T.leaves, leafSet b.1) ≤ ε * T.leafLength :=
  (measure_mono (T.leafUnion_subset_firstGoodUnion hg leafSet goodSet hcover)).trans
    (T.measure_firstGoodUnion_le h μ goodSet ε hgood)

/-- The form used for the scalar projection of the final segment
union. A good ancestor's projected tube covers each of its final
descendants and has measure at most `ε` times the ancestor length. -/
theorem volume_projected_leafUnion_le
    (T : VenetianBlindTree) (h : T.LengthExpanding) (hg : T.GoodOnEveryBranch)
    (φ : Plane → ℝ) (segments tubes : List ℕ → Set Plane) (ε : ℝ≥0∞)
    (hcover : ∀ a ∈ T.firstGood, ∀ b ∈ T.leaves, a.1 <+: b.1 →
      φ '' segments b.1 ⊆ φ '' tubes a.1)
    (hgood : ∀ a ∈ T.firstGood, volume (φ '' tubes a.1) ≤ ε * a.2) :
    volume (φ '' (⋃ b ∈ T.leaves, segments b.1)) ≤ ε * T.leafLength := by
  simp only [image_iUnion]
  exact T.measure_leafUnion_le h hg volume
    (fun p => φ '' segments p) (fun p => φ '' tubes p) ε hcover hgood

end VenetianBlindTree

/-- Finite local length-inflation factors have an exponential bound
depending on the total increment, not the number of refinements. -/
theorem finite_blind_inflation_product_le_exp
    {ι : Type*} (s : Finset ι) (δ : ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hδ : ∀ i ∈ s, 0 ≤ δ i) :
    ∏ i ∈ s, (1 + C * δ i) ≤ Real.exp (C * ∑ i ∈ s, δ i) := by
  calc
    ∏ i ∈ s, (1 + C * δ i) ≤ ∏ i ∈ s, Real.exp (C * δ i) :=
      Finset.prod_le_prod (fun i hi => by have := hδ i hi; positivity)
        (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (C * δ i))
    _ = Real.exp (∑ i ∈ s, C * δ i) := (Real.exp_sum s _).symm
    _ = Real.exp (C * ∑ i ∈ s, δ i) := by rw [Finset.mul_sum]

/-- The recursive total-length estimate is proved by finite induction. -/
theorem finite_blind_length_le_product
    (L δ : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hδ : ∀ n, 0 ≤ δ n)
    (hstep : ∀ n, L (n + 1) ≤ (1 + C * δ n) * L n)
    (n : ℕ) :
    L n ≤ L 0 * ∏ i ∈ Finset.range n, (1 + C * δ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      L (n + 1) ≤ (1 + C * δ n) * L n := hstep n
      _ ≤ (1 + C * δ n) * (L 0 * ∏ i ∈ Finset.range n, (1 + C * δ i)) :=
        mul_le_mul_of_nonneg_left ih (by have := hδ n; positivity)
      _ = L 0 * ∏ i ∈ Finset.range (n + 1), (1 + C * δ i) := by
        rw [Finset.prod_range_succ]
        ring

/-- Uniform final length when the total parameter rotation is bounded.
The estimate is independent of the number of subdivision stages. -/
theorem finite_blind_length_le_exp
    (L δ : ℕ → ℝ) (C R : ℝ) (hL₀ : 0 ≤ L 0) (hC : 0 ≤ C)
    (hδ : ∀ n, 0 ≤ δ n)
    (hstep : ∀ n, L (n + 1) ≤ (1 + C * δ n) * L n)
    (n : ℕ) (hspan : ∑ i ∈ Finset.range n, δ i ≤ R) :
    L n ≤ L 0 * Real.exp (C * R) := by
  calc
    L n ≤ L 0 * ∏ i ∈ Finset.range n, (1 + C * δ i) :=
      finite_blind_length_le_product L δ C hC hδ hstep n
    _ ≤ L 0 * Real.exp (C * ∑ i ∈ Finset.range n, δ i) :=
      mul_le_mul_of_nonneg_left
        (finite_blind_inflation_product_le_exp (Finset.range n) δ C hC (fun i _ => hδ i)) hL₀
    _ ≤ L 0 * Real.exp (C * R) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hspan hC)) hL₀

end PlanarNikodym
