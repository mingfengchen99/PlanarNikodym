import PlanarNikodym.Projection.BlindSegmentSubdivision
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Actual finite iterations of nonlinear segment replacements.

The finite index of a new generation is a dependent pair consisting of
its parent and a dyadic center. Thus coincident geometric segments do not
erase parent information. Each replacement depth is chosen using the
proved dyadic construction, compactness inside the open domain, and the
decay of the dyadic half-lengths.
-/

noncomputable section
open Set Metric Filter
open scoped Topology BigOperators

namespace PlanarNikodym

/-- A finite indexed family. Distinct indices may represent coincident
segments; this preserves their separate parents and length budgets. -/
structure FiniteBlindFamily (E : Type) where
  Index : Type
  finite : Fintype Index
  center : Index → E
  halfLength : Index → ℝ

attribute [instance] FiniteBlindFamily.finite

namespace FiniteBlindFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def carrier (P : FiniteBlindFamily E) (v : E) : Set E :=
  ⋃ i, centeredBlindSegment (P.center i) v (P.halfLength i)

def budget (P : FiniteBlindFamily E) : ℝ :=
  ∑ i, P.halfLength i

def singleton (c : E) (a : ℝ) : FiniteBlindFamily E where
  Index := Unit
  finite := inferInstance
  center := fun _ => c
  halfLength := fun _ => a

@[simp] theorem carrier_singleton (c v : E) (a : ℝ) :
    (singleton c a).carrier v = centeredBlindSegment c v a := by
  change (⋃ _i : Unit, centeredBlindSegment c v a) = centeredBlindSegment c v a
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
    exact hx
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨(), hx⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem budget_singleton (c : E) (a : ℝ) :
    (singleton c a).budget = a := by
  simp [budget, singleton]

theorem isCompact_carrier (P : FiniteBlindFamily E) (v : E) :
    IsCompact (P.carrier v) :=
  isCompact_iUnion (fun i => isCompact_centeredBlindSegment (P.center i) v (P.halfLength i))

end FiniteBlindFamily

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Choosing an actual depth simultaneously makes the new half-length
small and keeps every new segment inside a specified open domain and
near its original parent. -/
theorem exists_blind_depth_in_open
    {S : Set E} (hS : IsOpen S) (c v w : E) (a Λ ε ζ : ℝ)
    (ha : 0 ≤ a) (hε : 0 < ε) (hζ : 0 < ζ)
    (hc : centeredBlindSegment c v a ⊆ S) :
    ∃ n : ℕ, Λ * (a / (2 : ℝ) ^ n) < ζ ∧
      (∀ z ∈ dyadicBlindCenters c v a n,
        centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n)) ⊆ S) ∧
      ∀ z ∈ dyadicBlindCenters c v a n,
        ∀ x ∈ centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n)),
          ∃ y ∈ centeredBlindSegment c v a, dist x y < ε := by
  obtain ⟨δ, hδ, hbuffer⟩ :=
    (isCompact_centeredBlindSegment c v a).exists_thickening_subset_open hS hc
  have ht : Tendsto (fun n : ℕ => Λ * (a / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_dyadicBlind_halfLength_zero a).const_mul Λ
  have hd : Tendsto (fun n : ℕ => Λ * (a / (2 : ℝ) ^ n) * ‖w‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using ht.mul_const ‖w‖
  obtain ⟨n, hn, hdist⟩ := ((ht.eventually (gt_mem_nhds hζ)).and
    (hd.eventually (gt_mem_nhds (lt_min hδ hε)))).exists
  have hclose (z : E) (hz : z ∈ dyadicBlindCenters c v a n) (x : E)
      (hx : x ∈ centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n))) :
      ∃ y ∈ centeredBlindSegment c v a, dist x y < min δ ε := by
    obtain ⟨y, hy, hxy⟩ := rotated_dyadicBlindSubdivision_close c v w a Λ ha n
      (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hx⟩⟩)
    exact ⟨y, hy, hxy.trans_lt hdist⟩
  refine ⟨n, hn, ?_, ?_⟩
  · intro z hz x hx
    obtain ⟨y, hy, hxy⟩ := hclose z hz x hx
    exact hbuffer (mem_thickening_iff.mpr ⟨y, hy, hxy.trans_le (min_le_left _ _)⟩)
  · intro z hz x hx
    obtain ⟨y, hy, hxy⟩ := hclose z hz x hx
    exact ⟨y, hy, hxy.trans_le (min_le_right _ _)⟩

/-- The actual next generation, with an explicit parent index in each
dependent pair. -/
def dyadicBlindGeneration (P : FiniteBlindFamily E) (v : E) (Λ : ℝ)
    (depth : P.Index → ℕ) : FiniteBlindFamily E where
  Index := Σ i : P.Index, ↥(dyadicBlindCenters (P.center i) v (P.halfLength i) (depth i))
  finite := inferInstance
  center := fun j => j.2.val
  halfLength := fun j => Λ * (P.halfLength j.1 / (2 : ℝ) ^ depth j.1)

def dyadicBlindParent (P : FiniteBlindFamily E) (v : E) (Λ : ℝ)
    (depth : P.Index → ℕ) :
    (dyadicBlindGeneration P v Λ depth).Index → P.Index :=
  Sigma.fst

theorem dyadicBlindGeneration_budget_le (P : FiniteBlindFamily E) (v : E) (Λ : ℝ)
    (depth : P.Index → ℕ) (hP : ∀ i, 0 ≤ P.halfLength i) (hΛ : 0 ≤ Λ) :
    (dyadicBlindGeneration P v Λ depth).budget ≤ Λ * P.budget := by
  classical
  change (∑ j : Σ i : P.Index,
      ↥(dyadicBlindCenters (P.center i) v (P.halfLength i) (depth i)),
      Λ * (P.halfLength j.1 / (2 : ℝ) ^ depth j.1)) ≤ Λ * ∑ i, P.halfLength i
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  dsimp only
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] using
    dyadicBlindCenters_expanded_halfLength_budget (P.center i) v
    (P.halfLength i) Λ (hP i) hΛ (depth i)

theorem dyadicBlindGeneration_center_mem_parent
    (P : FiniteBlindFamily E) (v : E) (Λ : ℝ) (depth : P.Index → ℕ)
    (hP : ∀ i, 0 ≤ P.halfLength i) (j : (dyadicBlindGeneration P v Λ depth).Index) :
    (dyadicBlindGeneration P v Λ depth).center j ∈
      centeredBlindSegment (P.center (dyadicBlindParent P v Λ depth j)) v
        (P.halfLength (dyadicBlindParent P v Λ depth j)) :=
  dyadicBlindCenters_subset_centeredBlindSegment (P.center j.1) v
    (P.halfLength j.1) (hP j.1) (depth j.1) j.2.property

theorem dyadicBlindGeneration_halfLength_pos
    (P : FiniteBlindFamily E) (v : E) (Λ : ℝ) (depth : P.Index → ℕ)
    (hP : ∀ i, 0 < P.halfLength i) (hΛ : 0 < Λ)
    (j : (dyadicBlindGeneration P v Λ depth).Index) :
    0 < (dyadicBlindGeneration P v Λ depth).halfLength j :=
  mul_pos hΛ (div_pos (hP j.1) (by positivity))

/-- Exact child budget at each parent, with children kept as separate
dependent indices even if different parents overlap geometrically. -/
theorem dyadicBlindGeneration_parent_budget
    (P : FiniteBlindFamily E) (v : E) (Λ : ℝ) (depth : P.Index → ℕ)
    (hP : ∀ i, 0 < P.halfLength i) (hv : v ≠ 0) (i : P.Index) :
    (∑ z : ↥(dyadicBlindCenters (P.center i) v (P.halfLength i) (depth i)),
      (dyadicBlindGeneration P v Λ depth).halfLength ⟨i, z⟩) = Λ * P.halfLength i := by
  change (∑ _z : ↥(dyadicBlindCenters (P.center i) v (P.halfLength i) (depth i)),
    Λ * (P.halfLength i / (2 : ℝ) ^ depth i)) = Λ * P.halfLength i
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] using
    dyadicBlindCenters_expanded_halfLength_eq (P.center i) v
    (P.halfLength i) Λ (hP i) hv (depth i)

theorem dyadicBlindGeneration_budget_eq
    (P : FiniteBlindFamily E) (v : E) (Λ : ℝ) (depth : P.Index → ℕ)
    (hP : ∀ i, 0 < P.halfLength i) (hv : v ≠ 0) :
    (dyadicBlindGeneration P v Λ depth).budget = Λ * P.budget := by
  classical
  change (∑ j : Σ i : P.Index,
      ↥(dyadicBlindCenters (P.center i) v (P.halfLength i) (depth i)),
      Λ * (P.halfLength j.1 / (2 : ℝ) ^ depth j.1)) = Λ * ∑ i, P.halfLength i
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact dyadicBlindGeneration_parent_budget P v Λ depth hP hv i

/-- A finite construction certificate that retains every generation and
its actual dyadic subdivision depths. A child index contains its parent
as its first component. The initial constructor permits exact
subdivision in the original direction, without paying a length factor. -/
inductive DyadicBlindTrace (P₀ : FiniteBlindFamily E) (v : ℕ → E) (Λ : ℕ → ℝ) :
    (n : ℕ) → FiniteBlindFamily E → Type 1
  | initial (depth : P₀.Index → ℕ) :
      DyadicBlindTrace P₀ v Λ 0 (dyadicBlindGeneration P₀ (v 0) 1 depth)
  | step {n : ℕ} {P : FiniteBlindFamily E}
      (previous : DyadicBlindTrace P₀ v Λ n P)
      (depth : P.Index → ℕ) (ε : P.Index → ℝ) (hε : ∀ i, 0 < ε i)
      (close : ∀ j : (dyadicBlindGeneration P (v n) (Λ n) depth).Index,
        ∀ x ∈ centeredBlindSegment
          ((dyadicBlindGeneration P (v n) (Λ n) depth).center j) (v (n + 1))
          ((dyadicBlindGeneration P (v n) (Λ n) depth).halfLength j),
        ∃ y ∈ centeredBlindSegment (P.center j.1) (v n) (P.halfLength j.1),
          dist x y < ε j.1) :
      DyadicBlindTrace P₀ v Λ (n + 1) (dyadicBlindGeneration P (v n) (Λ n) depth)

namespace DyadicBlindTrace
variable {P₀ : FiniteBlindFamily E} {v : ℕ → E} {Λ : ℕ → ℝ}

def family {n : ℕ} {Q : FiniteBlindFamily E} (_trace : DyadicBlindTrace P₀ v Λ n Q) :
    FiniteBlindFamily E := Q

def level {n : ℕ} {Q : FiniteBlindFamily E} (_trace : DyadicBlindTrace P₀ v Λ n Q) :
    ℕ := n

/-- Every recorded generation stays inside the analytic domain. -/
def InDomain {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (S : Set E) : Prop :=
  match trace with
  | .initial _ => Q.carrier (v n) ⊆ S
  | .step previous _ _ _ _ => previous.InDomain S ∧ Q.carrier (v n) ⊆ S

/-- Every generation, rather than only the terminal generation, has
half-length smaller than the same prescribed threshold. -/
def AllHalfLengthLT {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (ζ : ℝ) : Prop :=
  match trace with
  | .initial _ => ∀ j, Q.halfLength j < ζ
  | .step previous _ _ _ _ => previous.AllHalfLengthLT ζ ∧ ∀ j, Q.halfLength j < ζ

/-- Every child, including each initial exact subdivision piece, is at
most a prescribed fraction of its own parent half-length. -/
def Shrinks {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q) (β : ℝ) : Prop :=
  match trace with
  | .initial depth =>
      ∀ j : (dyadicBlindGeneration P₀ (v 0) 1 depth).Index,
        (dyadicBlindGeneration P₀ (v 0) 1 depth).halfLength j ≤ β * P₀.halfLength j.1
  | .step previous depth _ _ _ => previous.Shrinks β ∧
      ∀ j : (dyadicBlindGeneration previous.family (v previous.level)
          (Λ previous.level) depth).Index,
        (dyadicBlindGeneration previous.family (v previous.level)
          (Λ previous.level) depth).halfLength j ≤ β * previous.family.halfLength j.1

theorem halfLength_pos {n : ℕ} {Q : FiniteBlindFamily E}
    (trace : DyadicBlindTrace P₀ v Λ n Q)
    (hP : ∀ i, 0 < P₀.halfLength i) (hΛ : ∀ k < n, 0 < Λ k) :
    ∀ j, 0 < Q.halfLength j := by
  induction trace with
  | initial depth =>
      exact dyadicBlindGeneration_halfLength_pos P₀ (v 0) 1 depth hP zero_lt_one
  | @step n P previous depth ε hε close ih =>
      exact dyadicBlindGeneration_halfLength_pos P (v n) (Λ n) depth
        (ih (fun k hk => hΛ k (hk.trans (Nat.lt_succ_self n))))
        (hΛ n (Nat.lt_succ_self n))

end DyadicBlindTrace

/-- A real next generation for a whole finite family. The depth of each
parent's subdivision is selected from the proved construction, and the
same resulting generation preserves every projection in the family. -/
theorem exists_blind_generation_variable
    {ι : Type*} (f : ι → E → ℝ) (P : FiniteBlindFamily E)
    {S : Set E} {v w : E} {m M η Λ : ℝ} (ε ζ : P.Index → ℝ)
    (hopen : IsOpen S) (hconv : Convex ℝ S)
    (hP : ∀ i, 0 ≤ P.halfLength i) (hPS : P.carrier v ⊆ S)
    (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hΛ : 1 + M / m * η ≤ Λ) (hvw : ‖w - v‖ ≤ η)
    (hf : ∀ i z, z ∈ S → DifferentiableAt ℝ (f i) z)
    (hd : ∀ i z, z ∈ S → m ≤ fderiv ℝ (f i) z w)
    (hbound : ∀ i z, z ∈ S → ‖fderiv ℝ (f i) z‖ ≤ M)
    (hε : ∀ i, 0 < ε i) (hζ : ∀ i, 0 < ζ i) :
    ∃ depth : P.Index → ℕ,
      let Q := dyadicBlindGeneration P v Λ depth
      (∀ j, 0 ≤ Q.halfLength j ∧ Q.halfLength j <
        ζ (dyadicBlindParent P v Λ depth j)) ∧
      Q.carrier w ⊆ S ∧
      (∀ j, ∀ x ∈ centeredBlindSegment (Q.center j) w (Q.halfLength j),
        ∃ y ∈ centeredBlindSegment (P.center (dyadicBlindParent P v Λ depth j)) v
          (P.halfLength (dyadicBlindParent P v Λ depth j)),
            dist x y < ε (dyadicBlindParent P v Λ depth j)) ∧
      Q.budget ≤ Λ * P.budget ∧
      ∀ i, f i '' P.carrier v ⊆ f i '' Q.carrier w := by
  classical
  have hparent (i : P.Index) :
      centeredBlindSegment (P.center i) v (P.halfLength i) ⊆ S :=
    fun x hx => hPS (Set.mem_iUnion.mpr ⟨i, hx⟩)
  have hex (i : P.Index) := exists_blind_depth_in_open hopen (P.center i) v w
    (P.halfLength i) Λ (ε i) (ζ i) (hP i) (hε i) (hζ i) (hparent i)
  choose depth hsmall hinside hclose using hex
  have hΛzero : 0 ≤ Λ := le_trans (by positivity) hΛ
  refine ⟨depth, ?_, ?_, ?_, dyadicBlindGeneration_budget_le P v Λ depth hP hΛzero, ?_⟩
  · intro j
    exact ⟨mul_nonneg hΛzero (div_nonneg (hP j.1) (by positivity)), hsmall j.1⟩
  · intro x hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    exact hinside j.1 j.2.val j.2.property hx
  · intro j x hx
    exact hclose j.1 j.2.val j.2.property x hx
  · intro i
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    have himage := image_centeredBlindSegment_subset_rotated_dyadic
      (hP p) hm hM hη hΛ hvw hconv (hf i) (hd i) (hbound i)
      (hparent p) (depth p) (hinside p)
    obtain ⟨y, hy, he⟩ := himage (show f i x ∈
      f i '' centeredBlindSegment (P.center p) v (P.halfLength p) from ⟨x, hp, rfl⟩)
    obtain ⟨z, hz, hzy⟩ : ∃ z ∈ dyadicBlindCenters (P.center p) v
        (P.halfLength p) (depth p),
        y ∈ centeredBlindSegment z w (Λ * (P.halfLength p / (2 : ℝ) ^ depth p)) := by
      simpa only [Set.mem_iUnion, exists_prop] using hy
    exact ⟨y, Set.mem_iUnion.mpr ⟨⟨p, z, hz⟩, hzy⟩, he⟩

/-- The length growth over finitely many direction changes is controlled
by the exponential of their total variation. -/
theorem blindExpansionProduct_le_exp (C : ℝ) (hC : 0 ≤ C) (δ : ℕ → ℝ)
    (n : ℕ) (hδ : ∀ k < n, 0 ≤ δ k) :
    (∏ k ∈ Finset.range n, (1 + C * δ k)) ≤
      Real.exp (C * ∑ k ∈ Finset.range n, δ k) := by
  calc
    _ ≤ ∏ k ∈ Finset.range n, Real.exp (C * δ k) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact add_nonneg zero_le_one (mul_nonneg hC (hδ k (Finset.mem_range.mp hk)))
      · intro k _
        simpa only [add_comm] using Real.add_one_le_exp (C * δ k)
    _ = Real.exp (∑ k ∈ Finset.range n, C * δ k) := (Real.exp_sum _ _).symm
    _ = _ := by rw [Finset.mul_sum]

/-- A genuine finite multi-round construction. The terminal generation
has the final direction, arbitrarily short pieces, preserved projections,
and a recorded sequence of actual dyadic parent/child refinements.
Its total parameter half-length is exactly the product of the expansion
factors; no existence of a replacement step is assumed. -/
theorem exists_iterated_blind_replacement_shrinking
    {ι : Type*} (f : ι → E → ℝ) (P₀ : FiniteBlindFamily E)
    (v : ℕ → E) (δ : ℕ → ℝ) {S : Set E} {m M : ℝ}
    (hopen : IsOpen S) (hconv : Convex ℝ S)
    (hP : ∀ i, 0 < P₀.halfLength i) (hPS : P₀.carrier (v 0) ⊆ S)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ i z, z ∈ S → DifferentiableAt ℝ (f i) z)
    (hbound : ∀ i z, z ∈ S → ‖fderiv ℝ (f i) z‖ ≤ M)
    (n : ℕ) (hv : ∀ k ≤ n, v k ≠ 0)
    (hd : ∀ k ≤ n, ∀ i z, z ∈ S → m ≤ fderiv ℝ (f i) z (v k))
    (hδ : ∀ k < n, 0 ≤ δ k)
    (hstep : ∀ k < n, ‖v (k + 1) - v k‖ ≤ δ k)
    (β ε ζ : ℝ) (hβ : 0 < β) (hε : 0 < ε) (hζ : 0 < ζ) :
    ∃ Q : FiniteBlindFamily E,
      (∃ trace : DyadicBlindTrace P₀ v (fun k => 1 + M / m * δ k) n Q,
        trace.InDomain S ∧ trace.Shrinks β ∧ trace.AllHalfLengthLT ζ) ∧
      (∀ j, 0 < Q.halfLength j ∧ Q.halfLength j < ζ) ∧
      Q.carrier (v n) ⊆ S ∧
      (∀ x ∈ Q.carrier (v n), ∃ y ∈ P₀.carrier (v 0), dist x y < ε) ∧
      Q.budget = P₀.budget * ∏ k ∈ Finset.range n, (1 + M / m * δ k) ∧
      ∀ i, f i '' P₀.carrier (v 0) ⊆ f i '' Q.carrier (v n) := by
  classical
  induction n generalizing ε ζ with
  | zero =>
      obtain ⟨depth, hsmall, hinside, hclose, _, hcover⟩ :=
        exists_blind_generation_variable (v := v 0) (w := v 0) (Λ := 1) (η := 0)
          f P₀ (fun _ => ε) (fun i => min ζ (β * P₀.halfLength i)) hopen hconv
          (fun i => (hP i).le) hPS hm hM le_rfl (by simp) (by simp)
          hf (hd 0 le_rfl) hbound (fun _ => hε) (fun i => lt_min hζ (mul_pos hβ (hP i)))
      refine ⟨dyadicBlindGeneration P₀ (v 0) 1 depth,
        ⟨.initial depth, hinside, ?_, ?_⟩,
        ?_, hinside, ?_, ?_, hcover⟩
      · intro j
        exact (hsmall j).2.le.trans (min_le_right _ _)
      · intro j
        exact (hsmall j).2.trans_le (min_le_left _ _)
      · intro j
        exact ⟨dyadicBlindGeneration_halfLength_pos P₀ (v 0) 1 depth hP zero_lt_one j,
          (hsmall j).2.trans_le (min_le_left _ _)⟩
      · intro x hx
        obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨y, hy, hxy⟩ := hclose j x hx
        exact ⟨y, Set.mem_iUnion.mpr ⟨j.1, hy⟩, hxy⟩
      · simpa using dyadicBlindGeneration_budget_eq P₀ (v 0) 1 depth hP (hv 0 le_rfl)
  | succ n ih =>
      have hvn : ∀ k ≤ n, v k ≠ 0 := fun k hk => hv k (hk.trans (Nat.le_succ n))
      have hdn : ∀ k ≤ n, ∀ i z, z ∈ S → m ≤ fderiv ℝ (f i) z (v k) :=
        fun k hk => hd k (hk.trans (Nat.le_succ n))
      obtain ⟨P, ⟨trace, htraceDomain, htraceShrink, htraceShort⟩,
          hpositive, hinside, hclose, hbudget, hcover⟩ :=
        ih hvn hdn (fun k hk => hδ k (hk.trans (Nat.lt_succ_self n)))
          (fun k hk => hstep k (hk.trans (Nat.lt_succ_self n)))
          (ε / 2) ζ (half_pos hε) hζ
      let Λ := 1 + M / m * δ n
      have hΛ : 0 < Λ := by
        dsimp [Λ]
        have := mul_nonneg (div_nonneg hM hm.le) (hδ n (Nat.lt_succ_self n))
        positivity
      obtain ⟨depth, hsmall, hinside', hclose', _, hcover'⟩ :=
        exists_blind_generation_variable (v := v n) (w := v (n + 1)) (Λ := Λ)
          f P (fun _ => ε / 2) (fun i => min ζ (β * P.halfLength i)) hopen hconv
          (fun i => (hpositive i).1.le) hinside hm hM (hδ n (Nat.lt_succ_self n))
          le_rfl (hstep n (Nat.lt_succ_self n)) hf (hd (n + 1) le_rfl) hbound
          (fun _ => half_pos hε) (fun i => lt_min hζ (mul_pos hβ (hpositive i).1))
      refine ⟨dyadicBlindGeneration P (v n) Λ depth,
        ⟨.step trace depth (fun _ => ε / 2) (fun _ => half_pos hε) hclose',
          ⟨htraceDomain, hinside'⟩, ⟨htraceShrink, ?_⟩, htraceShort, ?_⟩,
        ?_, hinside', ?_, ?_, ?_⟩
      · intro j
        exact (hsmall j).2.le.trans (min_le_right _ _)
      · intro j
        exact (hsmall j).2.trans_le (min_le_left _ _)
      · intro j
        exact ⟨dyadicBlindGeneration_halfLength_pos P (v n) Λ depth
          (fun i => (hpositive i).1) hΛ j, (hsmall j).2.trans_le (min_le_left _ _)⟩
      · intro x hx
        obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨y, hy, hxy⟩ := hclose' j x hx
        obtain ⟨z, hz, hyz⟩ := hclose y (Set.mem_iUnion.mpr ⟨j.1, hy⟩)
        refine ⟨z, hz, ?_⟩
        have htri := dist_triangle x y z
        linarith
      · rw [dyadicBlindGeneration_budget_eq P (v n) Λ depth
          (fun i => (hpositive i).1) (hv n (Nat.le_succ n)),
          hbudget, Finset.prod_range_succ]
        dsimp [Λ]
        ring
      · intro i
        exact (hcover i).trans (hcover' i)

end PlanarNikodym
