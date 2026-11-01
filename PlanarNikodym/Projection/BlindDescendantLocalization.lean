import PlanarNikodym.Projection.ThinRectangleProjection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-! Localization of descendants in finite blind replacements.

Actual point-to-parent distances add along a finite chain. A summable
dyadic error budget keeps every descendant inside a thin tube about
its ancestor, as required by the good-ancestor compression argument.
-/

noncomputable section
open Set Metric
open scoped BigOperators

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Enlarging a thin tube by a metric error enlarges only its thickness. -/
theorem mem_thinSegmentTube_of_dist_le
    {p v x y : E} {ℓ w δ : ℝ}
    (hy : y ∈ thinSegmentTube p v ℓ w) (hxy : dist x y ≤ δ) :
    x ∈ thinSegmentTube p v ℓ (w + δ) := by
  obtain ⟨t, u, ht, hu, hye⟩ := hy
  refine ⟨t, u + (x - y), ht, ?_, ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add hu (by simpa only [dist_eq_norm] using hxy))
  · rw [hye]
    abel

omit [NormedSpace ℝ E] in
/-- Every terminal point has an actual ancestor at distance at most the
sum of the one-step errors. The witness is built by finite induction. -/
theorem exists_ancestor_of_finite_blind_refinements
    (S : ℕ → Set E) (δ : ℕ → ℝ)
    (hstep : ∀ n x, x ∈ S (n + 1) → ∃ y ∈ S n, dist x y ≤ δ n)
    (n : ℕ) :
    ∀ x ∈ S n, ∃ y ∈ S 0, dist x y ≤ ∑ k ∈ Finset.range n, δ k := by
  induction n with
  | zero =>
    intro x hx
    exact ⟨x, hx, by simp⟩
  | succ n ih =>
    intro x hx
    obtain ⟨z, hz, hxz⟩ := hstep n x hx
    obtain ⟨y, hy, hzy⟩ := ih z hz
    refine ⟨y, hy, ?_⟩
    calc
      dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ ≤ δ n + ∑ k ∈ Finset.range n, δ k := add_le_add hxz hzy
      _ = ∑ k ∈ Finset.range (n + 1), δ k := by rw [Finset.sum_range_succ, add_comm]

omit [NormedSpace ℝ E] in
/-- The same estimate started at any intermediate generation. -/
theorem exists_ancestor_of_finite_blind_refinements_from
    (S : ℕ → Set E) (δ : ℕ → ℝ)
    (hstep : ∀ n x, x ∈ S (n + 1) → ∃ y ∈ S n, dist x y ≤ δ n)
    (i n : ℕ) :
    ∀ x ∈ S (i + n), ∃ y ∈ S i,
      dist x y ≤ ∑ k ∈ Finset.range n, δ (i + k) := by
  simpa only [Nat.add_zero, Nat.add_assoc] using
    exists_ancestor_of_finite_blind_refinements
      (fun k => S (i + k)) (fun k => δ (i + k)) (fun k => hstep (i + k)) n

theorem finite_blind_descendants_subset_tube
    (S : ℕ → Set E) (δ : ℕ → ℝ)
    (hstep : ∀ n x, x ∈ S (n + 1) → ∃ y ∈ S n, dist x y ≤ δ n)
    {p v : E} {ℓ w : ℝ} (h₀ : S 0 ⊆ thinSegmentTube p v ℓ w) (n : ℕ) :
    S n ⊆ thinSegmentTube p v ℓ (w + ∑ k ∈ Finset.range n, δ k) := by
  intro x hx
  obtain ⟨y, hy, hdist⟩ := exists_ancestor_of_finite_blind_refinements S δ hstep n x hx
  exact mem_thinSegmentTube_of_dist_le (h₀ hy) hdist

/-- A dyadic allocation has a finite total budget independent of depth. -/
theorem finite_blind_dyadic_error_sum_le (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    ∑ k ∈ Finset.range n, b / 2 * (1 / (2 : ℝ)) ^ k ≤ b := by
  rw [← Finset.mul_sum]
  calc
    b / 2 * ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k ≤ b / 2 * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (by positivity)
    _ = b := by ring

/-- In particular, all finite descendants fit in a single prescribed
ancestor tube when the successive errors use this dyadic allocation. -/
theorem finite_blind_descendants_subset_fixed_tube
    (S : ℕ → Set E) {b : ℝ} (hb : 0 ≤ b)
    (hstep : ∀ n x, x ∈ S (n + 1) →
      ∃ y ∈ S n, dist x y ≤ b / 2 * (1 / (2 : ℝ)) ^ n)
    {p v : E} {ℓ w : ℝ} (h₀ : S 0 ⊆ thinSegmentTube p v ℓ w) (n : ℕ) :
    S n ⊆ thinSegmentTube p v ℓ (w + b) := by
  intro x hx
  obtain ⟨y, hy, hdist⟩ := exists_ancestor_of_finite_blind_refinements
    S (fun k => b / 2 * (1 / (2 : ℝ)) ^ k) hstep n x hx
  exact mem_thinSegmentTube_of_dist_le (h₀ hy)
    (hdist.trans (finite_blind_dyadic_error_sum_le b hb n))

/-- Closed thickening consumes only its stated amount of the ancestor
tube's reserved thickness. Compactness supplies an actual nearest point. -/
theorem cthickening_subset_blind_tube
    {F : Set E} (hF : IsCompact F) {p v : E} {ℓ w δ : ℝ} (hδ : 0 ≤ δ)
    (hsub : F ⊆ thinSegmentTube p v ℓ w) :
    cthickening δ F ⊆ thinSegmentTube p v ℓ (w + δ) := by
  rw [hF.cthickening_eq_biUnion_closedBall hδ]
  intro x hx
  obtain ⟨y, hy, hd⟩ := mem_iUnion₂.mp hx
  exact mem_thinSegmentTube_of_dist_le (hsub hy) hd

omit [NormedSpace ℝ E] in
/-- A finite compact fan can be thickened inside an arbitrary open
container, with any prescribed positive upper bound on the thickness.
Its interior retains the original fan. -/
theorem exists_compact_blind_thickening [ProperSpace E]
    {F U : Set E} (hF : IsCompact F) (hU : IsOpen U) (hFU : F ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ IsCompact (cthickening δ F) ∧
      F ⊆ interior (cthickening δ F) ∧ cthickening δ F ⊆ U := by
  obtain ⟨r, hr, hbuffer⟩ := hF.exists_cthickening_subset_open hU hFU
  let δ := min r ε
  have hδ : 0 < δ := lt_min hr hε
  exact ⟨δ, hδ, min_le_right _ _, hF.cthickening,
    (self_subset_thickening hδ F).trans (thickening_subset_interior_cthickening δ F),
    (cthickening_mono (min_le_left _ _) F).trans hbuffer⟩

end PlanarNikodym
