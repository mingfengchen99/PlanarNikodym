import PlanarNikodym.Projection.NonlinearBlindReplacement
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite dyadic subdivisions for the local Venetian-blind step.

The segments are actual images of real intervals. At depth `n` they have
parameter half-length `a / 2^n`; their union is exactly the old segment.
Repeated centers are removed by the finite set, so the total half-length
budget can only decrease. Rotating and expanding each subsegment then
stays within an explicit shrinking distance of the original segment.
-/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact bisection of a centered segment. -/
theorem centeredBlindSegment_split (c v : E) (a : ℝ) (ha : 0 ≤ a) :
    centeredBlindSegment c v a =
      centeredBlindSegment (c - (a / 2) • v) v (a / 2) ∪
        centeredBlindSegment (c + (a / 2) • v) v (a / 2) := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases h : s ≤ 0
    · left
      refine ⟨s + a / 2, ⟨by linarith [hs.1], by linarith⟩, ?_⟩
      module
    · right
      refine ⟨s - a / 2, ⟨by linarith, by linarith [hs.2]⟩, ?_⟩
      module
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · refine ⟨s - a / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      module
    · refine ⟨s + a / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      module

/-- Centers obtained by `n` successive exact bisections. -/
def dyadicBlindCenters (c v : E) (a : ℝ) : ℕ → Finset E
  | 0 => {c}
  | n + 1 => by
      classical
      exact dyadicBlindCenters (c - (a / 2) • v) v (a / 2) n ∪
        dyadicBlindCenters (c + (a / 2) • v) v (a / 2) n

private theorem dyadic_halfLength_succ (a : ℝ) (n : ℕ) :
    a / (2 : ℝ) ^ (n + 1) = (a / 2) / (2 : ℝ) ^ n := by
  rw [pow_succ, div_div]
  congr 1
  ring

/-- A point is in the original segment precisely when it belongs to one
of the finitely many subsegments. -/
theorem mem_dyadicBlindSubdivision_iff
    (c v : E) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (x : E) :
    (∃ z ∈ dyadicBlindCenters c v a n,
      x ∈ centeredBlindSegment z v (a / (2 : ℝ) ^ n)) ↔
      x ∈ centeredBlindSegment c v a := by
  classical
  induction n generalizing c a with
  | zero => simp [dyadicBlindCenters]
  | succ n ih =>
      simp only [dyadicBlindCenters, Finset.mem_union, or_and_right, exists_or,
        dyadic_halfLength_succ]
      rw [ih _ _ (by positivity), ih _ _ (by positivity), centeredBlindSegment_split c v a ha]
      rfl

theorem centeredBlindSegment_eq_iUnion_dyadic
    (c v : E) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    centeredBlindSegment c v a =
      ⋃ z ∈ dyadicBlindCenters c v a n,
        centeredBlindSegment z v (a / (2 : ℝ) ^ n) := by
  ext x
  simpa only [Set.mem_iUnion, exists_prop] using
    (mem_dyadicBlindSubdivision_iff c v a ha n x).symm

/-- Every subdivision center lies on the original segment. -/
theorem dyadicBlindCenters_subset_centeredBlindSegment
    (c v : E) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ↑(dyadicBlindCenters c v a n) ⊆ centeredBlindSegment c v a := by
  intro z hz
  apply (mem_dyadicBlindSubdivision_iff c v a ha n z).mp
  refine ⟨z, hz, ?_⟩
  simpa using mem_centeredBlindSegment z v
    (show |(0 : ℝ)| ≤ a / (2 : ℝ) ^ n by
      simpa using div_nonneg ha (show 0 ≤ (2 : ℝ) ^ n by positivity))

theorem dyadicBlindCenters_card_le (c v : E) (a : ℝ) (n : ℕ) :
    (dyadicBlindCenters c v a n).card ≤ 2 ^ n := by
  classical
  induction n generalizing c a with
  | zero => simp [dyadicBlindCenters]
  | succ n ih =>
      change (dyadicBlindCenters (c - (a / 2) • v) v (a / 2) n ∪
        dyadicBlindCenters (c + (a / 2) • v) v (a / 2) n).card ≤ 2 ^ (n + 1)
      calc
        _ ≤ (dyadicBlindCenters (c - (a / 2) • v) v (a / 2) n).card +
          (dyadicBlindCenters (c + (a / 2) • v) v (a / 2) n).card :=
            Finset.card_union_le _ _
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add (ih _ _) (ih _ _)
        _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_two]

/-- With positive half-length, every center is represented by a strictly
interior segment parameter. In particular the two half-trees cannot
share centers when the direction is nonzero. -/
theorem dyadicBlindCenters_mem_interior_parameter
    (c v : E) (a : ℝ) (ha : 0 < a) (n : ℕ) {z : E}
    (hz : z ∈ dyadicBlindCenters c v a n) :
    ∃ s ∈ Ioo (-a) a, c + s • v = z := by
  classical
  induction n generalizing c a with
  | zero =>
      simp only [dyadicBlindCenters, Finset.mem_singleton] at hz
      subst z
      exact ⟨0, ⟨by linarith, ha⟩, by simp⟩
  | succ n ih =>
      change z ∈ dyadicBlindCenters (c - (a / 2) • v) v (a / 2) n ∪
        dyadicBlindCenters (c + (a / 2) • v) v (a / 2) n at hz
      rcases Finset.mem_union.mp hz with hl | hr
      · obtain ⟨s, hs, he⟩ := ih (c - (a / 2) • v) (a / 2) (by positivity) hl
        refine ⟨s - a / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
        calc
          c + (s - a / 2) • v = c - (a / 2) • v + s • v := by module
          _ = z := he
      · obtain ⟨s, hs, he⟩ := ih (c + (a / 2) • v) (a / 2) (by positivity) hr
        refine ⟨s + a / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
        calc
          c + (s + a / 2) • v = c + (a / 2) • v + s • v := by module
          _ = z := he

theorem dyadicBlindCenters_halves_disjoint
    (c v : E) (a : ℝ) (ha : 0 < a) (hv : v ≠ 0) (n : ℕ) :
    Disjoint (dyadicBlindCenters (c - (a / 2) • v) v (a / 2) n)
      (dyadicBlindCenters (c + (a / 2) • v) v (a / 2) n) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hl hr
  obtain ⟨s, hs, he⟩ := dyadicBlindCenters_mem_interior_parameter
    (c - (a / 2) • v) v (a / 2) (by positivity) n hl
  obtain ⟨t, ht, hf⟩ := dyadicBlindCenters_mem_interior_parameter
    (c + (a / 2) • v) v (a / 2) (by positivity) n hr
  have heq : c + (s - a / 2) • v = c + (t + a / 2) • v := by
    calc
      c + (s - a / 2) • v = c - (a / 2) • v + s • v := by module
      _ = z := he
      _ = c + (a / 2) • v + t • v := hf.symm
      _ = c + (t + a / 2) • v := by module
  have hst : s - a / 2 = t + a / 2 :=
    smul_left_injective ℝ hv (add_left_cancel heq)
  linarith [hs.2, ht.1]

/-- A nondegenerate segment has exactly `2^n` distinct subdivision
centers, so it has no loss in total parameter length. -/
theorem dyadicBlindCenters_card_eq
    (c v : E) (a : ℝ) (ha : 0 < a) (hv : v ≠ 0) (n : ℕ) :
    (dyadicBlindCenters c v a n).card = 2 ^ n := by
  classical
  induction n generalizing c a with
  | zero => simp [dyadicBlindCenters]
  | succ n ih =>
      rw [dyadicBlindCenters, Finset.card_union_of_disjoint
        (dyadicBlindCenters_halves_disjoint c v a ha hv n),
        ih _ _ (by positivity), ih _ _ (by positivity)]
      simp [pow_succ, Nat.mul_two]

theorem dyadicBlindCenters_halfLength_eq
    (c v : E) (a : ℝ) (ha : 0 < a) (hv : v ≠ 0) (n : ℕ) :
    ∑ _z ∈ dyadicBlindCenters c v a n, a / (2 : ℝ) ^ n = a := by
  classical
  simp only [Finset.sum_const, nsmul_eq_mul, dyadicBlindCenters_card_eq c v a ha hv n,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem dyadicBlindCenters_expanded_halfLength_eq
    (c v : E) (a Λ : ℝ) (ha : 0 < a) (hv : v ≠ 0) (n : ℕ) :
    ∑ _z ∈ dyadicBlindCenters c v a n, Λ * (a / (2 : ℝ) ^ n) = Λ * a := by
  rw [← Finset.mul_sum, dyadicBlindCenters_halfLength_eq c v a ha hv n]

/-- The sum of parameter half-lengths does not exceed the original
half-length, even when some subdivision centers coincide. -/
theorem dyadicBlindCenters_halfLength_budget
    (c v : E) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ∑ _z ∈ dyadicBlindCenters c v a n, a / (2 : ℝ) ^ n ≤ a := by
  classical
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((dyadicBlindCenters c v a n).card : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast dyadicBlindCenters_card_le c v a n
  calc
    _ ≤ (2 : ℝ) ^ n * (a / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = a := by field_simp

/-- A rotated and expanded subsegment is close to its own center on the
original segment. The bound decreases with the subdivision depth. -/
theorem rotated_dyadicBlindSubdivision_close
    (c v w : E) (a Λ : ℝ) (ha : 0 ≤ a) (n : ℕ)
    {x : E}
    (hx : x ∈ ⋃ z ∈ dyadicBlindCenters c v a n,
      centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n))) :
    ∃ y ∈ centeredBlindSegment c v a,
      dist x y ≤ Λ * (a / (2 : ℝ) ^ n) * ‖w‖ := by
  obtain ⟨z, hz, s, hs, rfl⟩ : ∃ z ∈ dyadicBlindCenters c v a n,
      ∃ s ∈ Icc (-(Λ * (a / (2 : ℝ) ^ n))) (Λ * (a / (2 : ℝ) ^ n)),
        z + s • w = x := by
    simpa only [Set.mem_iUnion, centeredBlindSegment, Set.mem_image, exists_prop] using hx
  refine ⟨z, dyadicBlindCenters_subset_centeredBlindSegment c v a ha n hz, ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr hs) (norm_nonneg _)

theorem isCompact_rotated_dyadicBlindSubdivision
    (c v w : E) (a Λ : ℝ) (n : ℕ) :
    IsCompact (⋃ z ∈ dyadicBlindCenters c v a n,
      centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n))) :=
  (dyadicBlindCenters c v a n).isCompact_biUnion
    (fun z _ => isCompact_centeredBlindSegment z w _)

theorem dyadicBlindCenters_expanded_halfLength_budget
    (c v : E) (a Λ : ℝ) (ha : 0 ≤ a) (hΛ : 0 ≤ Λ) (n : ℕ) :
    ∑ _z ∈ dyadicBlindCenters c v a n, Λ * (a / (2 : ℝ) ^ n) ≤ Λ * a := by
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (dyadicBlindCenters_halfLength_budget c v a ha n) hΛ

theorem tendsto_dyadicBlind_halfLength_zero (a : ℝ) :
    Tendsto (fun n : ℕ => a / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 2⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)).const_mul a
  simpa only [mul_zero, div_eq_mul_inv, inv_pow] using h

/-- Any prescribed open neighbourhood of the original segment contains
all rotated subsegments after sufficiently many actual bisections. -/
theorem exists_rotated_dyadicBlindSubdivision_close
    (c v w : E) (a Λ ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x ∈ ⋃ z ∈ dyadicBlindCenters c v a n,
      centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n)),
      ∃ y ∈ centeredBlindSegment c v a, dist x y < ε := by
  have ht : Tendsto (fun n : ℕ => Λ * (a / (2 : ℝ) ^ n) * ‖w‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_dyadicBlind_halfLength_zero a).const_mul Λ).mul_const ‖w‖
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨n, fun x hx => ?_⟩
  obtain ⟨y, hy, hd⟩ := rotated_dyadicBlindSubdivision_close c v w a Λ ha n hx
  exact ⟨y, hy, hd.trans_lt hn⟩

/-- Applying the proved nonlinear one-segment replacement to every
member of the actual finite subdivision preserves the original image. -/
theorem image_centeredBlindSegment_subset_rotated_dyadic
    {f : E → ℝ} {S : Set E} {c v w : E} {a m M η Λ : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hΛ : 1 + M / m * η ≤ Λ) (hvw : ‖w - v‖ ≤ η)
    (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ S, m ≤ fderiv ℝ f z w)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ M)
    (hvS : centeredBlindSegment c v a ⊆ S) (n : ℕ)
    (hwS : ∀ z ∈ dyadicBlindCenters c v a n,
      centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n)) ⊆ S) :
    f '' centeredBlindSegment c v a ⊆
      f '' (⋃ z ∈ dyadicBlindCenters c v a n,
        centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n))) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hzx⟩ := (mem_dyadicBlindSubdivision_iff c v a ha n x).mpr hx
  have hold : centeredBlindSegment z v (a / (2 : ℝ) ^ n) ⊆ S := by
    intro y hy
    exact hvS ((mem_dyadicBlindSubdivision_iff c v a ha n y).mp ⟨z, hz, hy⟩)
  have himage := image_centeredBlindSegment_subset_of_direction_change
    (show 0 ≤ a / (2 : ℝ) ^ n by positivity) hm hM hη hΛ hvw
    hS hf hd hbound hold (hwS z hz)
  obtain ⟨y, hy, he⟩ := himage (show f x ∈ f '' centeredBlindSegment z v
    (a / (2 : ℝ) ^ n) from ⟨x, hzx, rfl⟩)
  exact ⟨y, Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hy⟩⟩, he⟩

/-- A finite nonlinear Venetian-blind step inside a prescribed tube.
The direction change preserves the complete scalar projection and costs
at most the explicit factor `Λ` in total parameter half-length. -/
theorem exists_finite_blind_replacement
    {f : E → ℝ} {S : Set E} {c v w : E} {a m M η Λ ε : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hΛ : 1 + M / m * η ≤ Λ) (hvw : ‖w - v‖ ≤ η)
    (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ S, m ≤ fderiv ℝ f z w)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ M)
    (hε : 0 < ε)
    (htube : ∀ x, (∃ y ∈ centeredBlindSegment c v a, dist x y < ε) → x ∈ S) :
    ∃ n : ℕ,
      (∀ x ∈ ⋃ z ∈ dyadicBlindCenters c v a n,
        centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n)),
        ∃ y ∈ centeredBlindSegment c v a, dist x y < ε) ∧
      (∑ _z ∈ dyadicBlindCenters c v a n, Λ * (a / (2 : ℝ) ^ n) ≤ Λ * a) ∧
      f '' centeredBlindSegment c v a ⊆
        f '' (⋃ z ∈ dyadicBlindCenters c v a n,
          centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n))) := by
  obtain ⟨n, hclose⟩ := exists_rotated_dyadicBlindSubdivision_close c v w a Λ ε ha hε
  have hΛzero : 0 ≤ Λ := le_trans (by positivity) hΛ
  refine ⟨n, hclose, dyadicBlindCenters_expanded_halfLength_budget c v a Λ ha hΛzero n, ?_⟩
  apply image_centeredBlindSegment_subset_rotated_dyadic
    ha hm hM hη hΛ hvw hS hf hd hbound
  · intro x hx
    exact htube x ⟨x, hx, by simpa using hε⟩
  · intro z hz x hx
    exact htube x (hclose x (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hx⟩⟩))

/-- One finite replacement preserves every member of a family whenever
the directional lower bound and derivative upper bound are uniform.
The chosen subdivision depth is shared by all projections. -/
theorem exists_finite_blind_replacement_family
    {ι : Type*} (f : ι → E → ℝ) {S : Set E} {c v w : E} {a m M η Λ ε : ℝ}
    (ha : 0 ≤ a) (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hΛ : 1 + M / m * η ≤ Λ) (hvw : ‖w - v‖ ≤ η)
    (hS : Convex ℝ S) (hf : ∀ i z, z ∈ S → DifferentiableAt ℝ (f i) z)
    (hd : ∀ i z, z ∈ S → m ≤ fderiv ℝ (f i) z w)
    (hbound : ∀ i z, z ∈ S → ‖fderiv ℝ (f i) z‖ ≤ M)
    (hε : 0 < ε)
    (htube : ∀ x, (∃ y ∈ centeredBlindSegment c v a, dist x y < ε) → x ∈ S) :
    ∃ n : ℕ,
      (∀ x ∈ ⋃ z ∈ dyadicBlindCenters c v a n,
        centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n)),
        ∃ y ∈ centeredBlindSegment c v a, dist x y < ε) ∧
      (∑ _z ∈ dyadicBlindCenters c v a n, Λ * (a / (2 : ℝ) ^ n) ≤ Λ * a) ∧
      ∀ i, f i '' centeredBlindSegment c v a ⊆
        f i '' (⋃ z ∈ dyadicBlindCenters c v a n,
          centeredBlindSegment z w (Λ * (a / (2 : ℝ) ^ n))) := by
  obtain ⟨n, hclose⟩ := exists_rotated_dyadicBlindSubdivision_close c v w a Λ ε ha hε
  have hΛzero : 0 ≤ Λ := le_trans (by positivity) hΛ
  refine ⟨n, hclose, dyadicBlindCenters_expanded_halfLength_budget c v a Λ ha hΛzero n, ?_⟩
  intro i
  apply image_centeredBlindSegment_subset_rotated_dyadic
    ha hm hM hη hΛ hvw hS (hf i) (hd i) (hbound i)
  · intro x hx
    exact htube x ⟨x, hx, by simpa using hε⟩
  · intro z hz x hx
    exact htube x (hclose x (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hx⟩⟩))

end PlanarNikodym
