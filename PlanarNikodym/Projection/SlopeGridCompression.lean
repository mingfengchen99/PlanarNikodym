import PlanarNikodym.Projection.ThinRectangleProjection
import Mathlib.Algebra.Order.Floor.Semiring

/-! Finite slope grids and actual selection of a compressible ancestor.

The grid is equispaced, contains both endpoints, and approximates every
slope in the interval. The final result selects its index using the actual
fiber slope at a common branch point and then applies thin-tube compression.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped Topology BigOperators

namespace PlanarNikodym

/-- The equispaced grid of `N + 1` points between `a` and `b`. -/
def uniformSlopeGrid (a b : ℝ) (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  a + (i.val : ℝ) * ((b - a) / (N : ℝ))

@[simp] theorem uniformSlopeGrid_zero (a b : ℝ) (N : ℕ) :
    uniformSlopeGrid a b N 0 = a := by
  simp [uniformSlopeGrid]

theorem uniformSlopeGrid_last (a b : ℝ) {N : ℕ} (hN : 0 < N) :
    uniformSlopeGrid a b N (Fin.last N) = b := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [uniformSlopeGrid, Fin.val_last]
  field_simp
  ring

theorem uniformSlopeGrid_monotone {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    Monotone (uniformSlopeGrid a b N) := by
  intro i j hij
  have hd : 0 ≤ (b - a) / (N : ℝ) :=
    div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  dsimp [uniformSlopeGrid]
  gcongr
  exact_mod_cast hij

theorem uniformSlopeGrid_strictMono {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) :
    StrictMono (uniformSlopeGrid a b N) := by
  intro i j hij
  have hd : 0 < (b - a) / (N : ℝ) :=
    div_pos (sub_pos.mpr hab) (Nat.cast_pos.mpr hN)
  dsimp [uniformSlopeGrid]
  gcongr
  exact_mod_cast hij

theorem uniformSlopeGrid_mem_Icc {a b : ℝ} (hab : a ≤ b) {N : ℕ}
    (hN : 0 < N) (i : Fin (N + 1)) :
    uniformSlopeGrid a b N i ∈ Icc a b := by
  have hm := uniformSlopeGrid_monotone hab N
  constructor
  · simpa using hm (Fin.zero_le i)
  · simpa only [uniformSlopeGrid_last a b hN] using hm (Fin.le_last i)

theorem uniformSlopeGrid_step (a b : ℝ) (N : ℕ) (i : Fin N) :
    uniformSlopeGrid a b N i.succ - uniformSlopeGrid a b N i.castSucc =
      (b - a) / (N : ℝ) := by
  simp only [uniformSlopeGrid, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- The entire variation budget is exactly the interval length, independently
of the number of grid steps. -/
theorem uniformSlopeGrid_total_variation {a b : ℝ} (hab : a ≤ b)
    {N : ℕ} (hN : 0 < N) :
    (∑ i : Fin N,
      |uniformSlopeGrid a b N i.succ - uniformSlopeGrid a b N i.castSucc|) = b - a := by
  have hstep : 0 ≤ (b - a) / (N : ℝ) :=
    div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [uniformSlopeGrid_step, abs_of_nonneg hstep, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Every slope is within one mesh length of an actual grid point.
The selected point is obtained from a bounded natural floor. -/
theorem exists_uniformSlopeGrid_near {a b s : ℝ} (hab : a ≤ b)
    {N : ℕ} (hN : 0 < N) (hs : s ∈ Icc a b) :
    ∃ i : Fin (N + 1), |s - uniformSlopeGrid a b N i| ≤ (b - a) / (N : ℝ) := by
  by_cases heq : a = b
  · subst b
    have hsa : s = a := le_antisymm hs.2 hs.1
    subst s
    exact ⟨0, by simp⟩
  have hgap : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  let d := (b - a) / (N : ℝ)
  have hd : 0 < d := div_pos hgap (Nat.cast_pos.mpr hN)
  have hNd : (N : ℝ) * d = b - a := by
    dsimp [d]
    field_simp
  have hratio₀ : 0 ≤ (s - a) / d := div_nonneg (sub_nonneg.mpr hs.1) hd.le
  have hratioN : (s - a) / d ≤ (N : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [hs.2]
  let n := Nat.floor ((s - a) / d)
  have hn : n ≤ N := Nat.floor_le_of_le hratioN
  let i : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hlo : (n : ℝ) * d ≤ s - a :=
    (le_div_iff₀ hd).mp (Nat.floor_le hratio₀)
  have hhi : s - a < ((n : ℝ) + 1) * d :=
    (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one ((s - a) / d))
  refine ⟨i, ?_⟩
  change |s - (a + (n : ℝ) * d)| ≤ d
  rw [abs_of_nonneg (by linarith)]
  nlinarith

/-- An actual finite mesh exists for every positive error tolerance. -/
theorem exists_uniformSlopeGrid_mesh {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ (b - a) / (N : ℝ) ≤ δ ∧
      Monotone (uniformSlopeGrid a b N) ∧
      uniformSlopeGrid a b N 0 = a ∧
      uniformSlopeGrid a b N (Fin.last N) = b ∧
      (∀ i, uniformSlopeGrid a b N i ∈ Icc a b) ∧
      ∀ s ∈ Icc a b, ∃ i, |s - uniformSlopeGrid a b N i| ≤ δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hN : 0 < n + 1 := Nat.succ_pos _
  have hmesh : (b - a) / ((n + 1 : ℕ) : ℝ) ≤ δ := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have hmul := (div_lt_iff₀ hδ).mp hn
    push_cast
    nlinarith
  refine ⟨n + 1, hN, hmesh, uniformSlopeGrid_monotone hab _,
    uniformSlopeGrid_zero _ _ _, uniformSlopeGrid_last _ _ hN,
    uniformSlopeGrid_mem_Icc hab hN, ?_⟩
  intro s hs
  obtain ⟨i, hi⟩ := exists_uniformSlopeGrid_near hab hN hs
  exact ⟨i, hi.trans hmesh⟩

/-- The actual fiber slope selects a grid direction with a small actual
spatial derivative. In particular, the index is not an assumed ancestor. -/
theorem exists_uniformSlopeGrid_small_tangent
    {φ : ℝ × Plane → ℝ} {p : ℝ × Plane} {a b H ε : ℝ} {N : ℕ}
    (hφ : DifferentiableAt ℝ φ p) (hh : scalarHeadDerivative φ p ≠ 0)
    (hH : 0 < H) (hhead : |scalarHeadDerivative φ p| ≤ H)
    (hab : a ≤ b) (hN : 0 < N)
    (hmesh : (b - a) / (N : ℝ) ≤ ε / (8 * H))
    (hslope : scalarGradientSlope φ p ∈ Icc a b) :
    ∃ i : Fin (N + 1),
      ‖fderiv ℝ (fun q : Plane => φ (p.1, q)) p.2
          (-uniformSlopeGrid a b N i, 1)‖ ≤ ε / 8 := by
  obtain ⟨i, hi⟩ := exists_uniformSlopeGrid_near hab hN hslope
  have hb := norm_scalar_slice_fderiv_slopeDirection_le hφ hh hhead (hi.trans hmesh)
  refine ⟨i, hb.trans_eq ?_⟩
  field_simp

/-- The full direction vector stays uniformly bounded on a bounded slope
interval, in the actual max norm on `Plane`. -/
theorem norm_slopeDirection_le_of_mem_Icc {a b s : ℝ} (hs : s ∈ Icc a b) :
    ‖((-s, 1) : Plane)‖ ≤ max (max |a| |b|) 1 := by
  have hsa : -max |a| |b| ≤ s :=
    (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le a).trans hs.1)
  have hsb : s ≤ max |a| |b| :=
    hs.2.trans ((le_abs_self b).trans (le_max_right _ _))
  have hsabs : |s| ≤ max |a| |b| := abs_le.mpr ⟨hsa, hsb⟩
  simpa only [Prod.norm_def, norm_neg, Real.norm_eq_abs, abs_one] using
    max_le_max hsabs (le_refl (1 : ℝ))

/-- Uniform construction of a finite grid and compression scales, followed
by actual selection of a compressible tube along every branch.

The branch is supplied only as centres and lengths of tubes, with a common
point `y`. Its direction at level `i` is the constructed grid direction.
The common point's true fiber slope chooses `i`; witness compression then
controls the entire ancestor tube. The doubled tubes remain
inside the compact convex buffer `K`, as required by that theorem. -/
theorem exists_uniformSlopeGrid_branch_compression
    {φ : ℝ × Plane → ℝ} {A : Set ℝ} {K : Set Plane}
    (hA : IsCompact A) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hφ : AnalyticOnNhd ℝ φ (A ×ˢ K))
    {a b H ε : ℝ} (hab : a ≤ b) (hH : 0 < H) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      (b - a) / (N : ℝ) ≤ ε / (8 * H) ∧
      Monotone (uniformSlopeGrid a b N) ∧
      uniformSlopeGrid a b N 0 = a ∧
      uniformSlopeGrid a b N (Fin.last N) = b ∧
      ∃ r > 0, ∃ η > 0, ∀ t ∈ A, ∀ y ∈ K,
        scalarHeadDerivative φ (t, y) ≠ 0 →
        |scalarHeadDerivative φ (t, y)| ≤ H →
        scalarGradientSlope φ (t, y) ∈ Icc a b →
        ∀ (c : Fin (N + 1) → Plane) (ℓ : Fin (N + 1) → ℝ),
          (∀ i, 0 ≤ ℓ i ∧ ℓ i ≤ r) →
          (∀ i, y ∈ thinSegmentTube (c i) (-uniformSlopeGrid a b N i, 1)
            (ℓ i) (η * ℓ i)) →
          (∀ i, thinSegmentTube y (-uniformSlopeGrid a b N i, 1)
            (2 * ℓ i) (η * (2 * ℓ i)) ⊆ K) →
          ∃ i : Fin (N + 1),
            volume ((fun q : Plane => φ (t, q)) ''
              thinSegmentTube (c i) (-uniformSlopeGrid a b N i, 1)
                (ℓ i) (η * ℓ i)) ≤ ENNReal.ofReal (ε * ℓ i) := by
  obtain ⟨N, hN, hmesh, hmono, hfirst, hlast, hgrid, _⟩ :=
    exists_uniformSlopeGrid_mesh hab (show 0 < ε / (8 * H) by positivity)
  let V := max (max |a| |b|) 1
  have hV : 0 ≤ V := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hdiff (t : ℝ) (ht : t ∈ A) (q : Plane) (hq : q ∈ K) :
      DifferentiableAt ℝ (fun q : Plane => φ (t, q)) q :=
    (hφ (t, q) ⟨ht, hq⟩).differentiableAt.comp q (by fun_prop)
  obtain ⟨r, hr, η, hη, hcompress⟩ :=
    exists_uniform_family_thinSegmentTube_compression_of_witness
      hA hK hconv hdiff (continuousOn_scalarSlice_fderiv_of_analyticOnNhd hφ) hV hε
  refine ⟨N, hN, hmesh, hmono, hfirst, hlast, r, hr, η, hη, ?_⟩
  intro t ht y hy hheadne hhead hslope c ℓ hlength hbranch hbuffer
  obtain ⟨i, hi⟩ := exists_uniformSlopeGrid_small_tangent
    (hφ (t, y) ⟨ht, hy⟩).differentiableAt hheadne hH hhead hab hN hmesh hslope
  exact ⟨i, hcompress t ht (c i) y (-uniformSlopeGrid a b N i, 1) (ℓ i)
    hy (hbranch i) (norm_slopeDirection_le_of_mem_Icc (hgrid i))
    (hlength i).1 (hlength i).2 hi (hbuffer i)⟩

end PlanarNikodym
