import PlanarNikodym.Projection.BlindDescendantLocalization
import PlanarNikodym.Projection.NonlinearBlindReplacement

/-! Actual ancestor tubes for geometrically shrinking blind branches.

Each child centre belongs to its parent segment. Thus a child point is at
distance at most the child's half-length times its direction norm from the
parent segment. Summing this genuine geometric error along a finite branch
places every terminal point in all of its ancestor tubes.
-/

noncomputable section
open Set Metric
open scoped BigOperators

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The relative geometric length bound holds from any intermediate level,
using only the finite prefix of the branch. -/
theorem shrinking_blind_length_le
    {a : ℕ → ℝ} {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (hstep : ∀ j < n, a (j + 1) ≤ β * a j)
    (i k : ℕ) (hik : i + k ≤ n) :
    a (i + k) ≤ β ^ k * a i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hik' : i + k ≤ n := by omega
    have hlt : i + k < n := by omega
    calc
      a (i + (k + 1)) ≤ β * a (i + k) := by
        simpa only [Nat.add_assoc] using hstep (i + k) hlt
      _ ≤ β * (β ^ k * a i) := mul_le_mul_of_nonneg_left (ih hik') hβ
      _ = β ^ (k + 1) * a i := by rw [pow_succ]; ring

/-- The complete descendant displacement budget is controlled relative to
the chosen ancestor; it does not depend on the depth of the branch. -/
theorem shrinking_blind_tail_sum_le
    {a : ℕ → ℝ} {β V : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2) (hV : 0 ≤ V)
    (hstep : ∀ j < n, a (j + 1) ≤ β * a j)
    (i k : ℕ) (hik : i + k ≤ n) (hai : 0 ≤ a i) :
    ∑ j ∈ Finset.range k, V * a (i + j + 1) ≤ 2 * V * β * a i := by
  have hb : 0 ≤ 2 * V * β * a i := by positivity
  refine (Finset.sum_le_sum (fun j hj => ?_)).trans
    (finite_blind_dyadic_error_sum_le (2 * V * β * a i) hb k)
  have hjk : j < k := Finset.mem_range.mp hj
  have hjn : i + (j + 1) ≤ n := by omega
  have hrel := shrinking_blind_length_le hβ hstep i (j + 1) hjn
  have hp : β ^ j ≤ (1 / (2 : ℝ)) ^ j := pow_le_pow_left₀ hβ hβhalf j
  calc
    V * a (i + j + 1) ≤ V * (β ^ (j + 1) * a i) := by
      apply mul_le_mul_of_nonneg_left _ hV
      simpa only [Nat.add_assoc] using hrel
    _ = (V * β * a i) * β ^ j := by rw [pow_succ]; ring
    _ ≤ (V * β * a i) * (1 / (2 : ℝ)) ^ j :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2 * V * β * a i) / 2 * (1 / (2 : ℝ)) ^ j := by ring

omit [NormedSpace ℝ E] in
/-- Finite-prefix form of the ancestor-distance induction; no hypotheses
about nonexistent generations beyond `n` are needed. -/
theorem exists_ancestor_of_bounded_blind_refinements
    (S : ℕ → Set E) (δ : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ k < n, ∀ x ∈ S (k + 1), ∃ y ∈ S k, dist x y ≤ δ k) :
    ∀ x ∈ S n, ∃ y ∈ S 0, dist x y ≤ ∑ k ∈ Finset.range n, δ k := by
  revert hstep
  induction n with
  | zero =>
    intro _ x hx
    exact ⟨x, hx, by simp⟩
  | succ n ih =>
    intro hstep x hx
    obtain ⟨z, hz, hxz⟩ := hstep n (Nat.lt_succ_self _) x hx
    obtain ⟨y, hy, hzy⟩ := ih (fun k hk => hstep k (by omega)) z hz
    refine ⟨y, hy, ?_⟩
    calc
      dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ ≤ δ n + ∑ k ∈ Finset.range n, δ k := add_le_add hxz hzy
      _ = ∑ k ∈ Finset.range (n + 1), δ k := by
        rw [Finset.sum_range_succ, add_comm]

theorem centeredBlindSegment_subset_thinSegmentTube (c v : E) (a : ℝ) :
    centeredBlindSegment c v a ⊆ thinSegmentTube c v (2 * a) 0 := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t, 0, ?_, by simp, by simp⟩
  have : |t| ≤ a := abs_le.mpr ht
  linarith

theorem dist_center_le_of_mem_centeredBlindSegment
    {c v y : E} {a V : ℝ} (ha : 0 ≤ a) (hv : ‖v‖ ≤ V)
    (hy : y ∈ centeredBlindSegment c v a) :
    dist y c ≤ V * a := by
  obtain ⟨t, ht, rfl⟩ := hy
  have ht' : |t| ≤ a := abs_le.mpr ht
  calc
    dist (c + t • v) c = |t| * ‖v‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    _ ≤ a * V := mul_le_mul ht' hv (norm_nonneg _) ha
    _ = V * a := mul_comm _ _

/-- Every terminal point of an actual geometrically shrinking branch lies
in the claimed tube about every ancestor segment. The thickness constant is
`2 * V * β`, with no supplied ancestor-neighbourhood hypothesis. -/
theorem shrinking_blind_descendant_mem_tube
    (c v : ℕ → E) (a : ℕ → ℝ) {n : ℕ} {β V : ℝ}
    (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2) (hV : 0 ≤ V)
    (ha : ∀ j ≤ n, 0 ≤ a j) (hv : ∀ j ≤ n, ‖v j‖ ≤ V)
    (hcenter : ∀ j < n, c (j + 1) ∈ centeredBlindSegment (c j) (v j) (a j))
    (hshrink : ∀ j < n, a (j + 1) ≤ β * a j)
    {y : E} (hy : y ∈ centeredBlindSegment (c n) (v n) (a n))
    (i : ℕ) (hi : i ≤ n) :
    y ∈ thinSegmentTube (c i) (v i) (2 * a i) (2 * V * β * a i) := by
  let S : ℕ → Set E := fun k =>
    centeredBlindSegment (c (i + k)) (v (i + k)) (a (i + k))
  let δ : ℕ → ℝ := fun k => V * a (i + k + 1)
  have hsteps : ∀ k < n - i, ∀ x ∈ S (k + 1),
      ∃ z ∈ S k, dist x z ≤ δ k := by
    intro k hk x hx
    have hlt : i + k < n := by omega
    have hle : i + k + 1 ≤ n := by omega
    refine ⟨c (i + k + 1), hcenter (i + k) hlt, ?_⟩
    apply dist_center_le_of_mem_centeredBlindSegment (ha _ hle) (hv _ hle)
    simpa only [S, Nat.add_assoc] using hx
  have hindex : i + (n - i) = n := by omega
  have hy' : y ∈ S (n - i) := by simpa only [S, hindex] using hy
  obtain ⟨z, hz, hdist⟩ :=
    exists_ancestor_of_bounded_blind_refinements S δ (n - i) hsteps y hy'
  have hz' : z ∈ thinSegmentTube (c i) (v i) (2 * a i) 0 :=
    centeredBlindSegment_subset_thinSegmentTube _ _ _ (by simpa only [S, Nat.add_zero] using hz)
  have hsum : ∑ k ∈ Finset.range (n - i), δ k ≤ 2 * V * β * a i :=
    shrinking_blind_tail_sum_le hβ hβhalf hV hshrink i (n - i)
      (by omega) (ha i hi)
  simpa only [zero_add] using mem_thinSegmentTube_of_dist_le hz' (hdist.trans hsum)

/-- A quantitative buffer for the doubled tube recentered at an arbitrary
point of the original tube. The factor three includes both the displacement
of the new centre and the radius of the doubled tube. -/
theorem recentered_double_tube_subset_closedBall
    {c v y q : E} {ℓ w R : ℝ}
    (hy : y ∈ thinSegmentTube c v ℓ w)
    (hbuffer : dist c q + 3 * (ℓ / 2 * ‖v‖ + w) ≤ R) :
    thinSegmentTube y v (2 * ℓ) (2 * w) ⊆ closedBall q R := by
  intro z hz
  rw [mem_closedBall]
  have hzy : dist z y ≤ (2 * ℓ) / 2 * ‖v‖ + 2 * w := by
    simpa only [dist_eq_norm] using thinSegmentTube_norm_sub_le hz
  have hyc : dist y c ≤ ℓ / 2 * ‖v‖ + w := by
    simpa only [dist_eq_norm] using thinSegmentTube_norm_sub_le hy
  calc
    dist z q ≤ dist z y + (dist y c + dist c q) :=
      (dist_triangle z y q).trans (add_le_add le_rfl (dist_triangle y c q))
    _ ≤ ((2 * ℓ) / 2 * ‖v‖ + 2 * w) + ((ℓ / 2 * ‖v‖ + w) + dist c q) := by
      gcongr
    _ = dist c q + 3 * (ℓ / 2 * ‖v‖ + w) := by ring
    _ ≤ R := hbuffer

/-- Centres in the half-radius ball and a uniform length/thickness budget
place every witness-centred doubled tube inside the required closed buffer.
This applies with `ℓ = 2a` and `w = 2Vβa` to the branch theorem above. -/
theorem recentered_double_tube_subset_closedBall_of_half_radius
    {c v y q : E} {ℓ w R V : ℝ}
    (hy : y ∈ thinSegmentTube c v ℓ w) (hℓ : 0 ≤ ℓ)
    (hv : ‖v‖ ≤ V) (hc : c ∈ closedBall q (R / 2))
    (hsize : 3 * (ℓ / 2 * V + w) ≤ R / 2) :
    thinSegmentTube y v (2 * ℓ) (2 * w) ⊆ closedBall q R := by
  apply recentered_double_tube_subset_closedBall hy
  have hc' : dist c q ≤ R / 2 := hc
  have hrad : ℓ / 2 * ‖v‖ + w ≤ ℓ / 2 * V + w := by gcongr
  linarith

end PlanarNikodym
