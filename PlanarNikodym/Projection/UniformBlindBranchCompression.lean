import PlanarNikodym.Projection.SlopeGridCompression
import PlanarNikodym.Projection.ShrinkingBlindBranch

/-! Assembly of actual finite-branch geometry and slope-grid compression.

The shrink factor and initial length threshold are chosen here. Membership
in every ancestor tube and the witness-centred buffer conditions are then
proved from child centres, length decay, and the half-radius domain.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped Topology

namespace PlanarNikodym

/-- Extend a finite branch by its final value. Only the valid prefix is used
in the geometric estimates below. -/
def finiteBlindBranchValue {X : Type*} {N : ℕ}
    (f : Fin (N + 1) → X) (j : ℕ) : X :=
  f ⟨min j N, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

@[simp] theorem finiteBlindBranchValue_coe {X : Type*} {N : ℕ}
    (f : Fin (N + 1) → X) (i : Fin (N + 1)) :
    finiteBlindBranchValue f i.val = f i := by
  dsimp only [finiteBlindBranchValue]
  congr 1
  exact Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ i.isLt))

theorem thinSegmentTube_mono_thickness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c v : E} {ℓ w w' : ℝ} (hw : w ≤ w') :
    thinSegmentTube c v ℓ w ⊆ thinSegmentTube c v ℓ w' := by
  rintro y ⟨t, u, ht, hu, he⟩
  exact ⟨t, u, ht, hu.trans hw, he⟩

/-- Finite-index version of the proved geometric branch estimate. -/
theorem shrinking_fin_blind_descendant_mem_tube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (c v : Fin (N + 1) → E) (a : Fin (N + 1) → ℝ)
    {β V : ℝ} (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2) (hV : 0 ≤ V)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, ‖v i‖ ≤ V)
    (hcenter : ∀ j : Fin N, c j.succ ∈
      centeredBlindSegment (c j.castSucc) (v j.castSucc) (a j.castSucc))
    (hshrink : ∀ j : Fin N, a j.succ ≤ β * a j.castSucc)
    {y : E} (hy : y ∈ centeredBlindSegment (c (Fin.last N)) (v (Fin.last N))
      (a (Fin.last N))) (i : Fin (N + 1)) :
    y ∈ thinSegmentTube (c i) (v i) (2 * a i) (2 * V * β * a i) := by
  have ha' (j : ℕ) (hj : j ≤ N) : 0 ≤ finiteBlindBranchValue a j := by
    simpa only [finiteBlindBranchValue, Nat.min_eq_left hj] using ha ⟨j, Nat.lt_succ_of_le hj⟩
  have hv' (j : ℕ) (hj : j ≤ N) : ‖finiteBlindBranchValue v j‖ ≤ V := by
    simpa only [finiteBlindBranchValue, Nat.min_eq_left hj] using hv ⟨j, Nat.lt_succ_of_le hj⟩
  have hc' (j : ℕ) (hj : j < N) :
      finiteBlindBranchValue c (j + 1) ∈
        centeredBlindSegment (finiteBlindBranchValue c j)
          (finiteBlindBranchValue v j) (finiteBlindBranchValue a j) := by
    let k : Fin N := ⟨j, hj⟩
    change finiteBlindBranchValue c k.succ.val ∈
      centeredBlindSegment (finiteBlindBranchValue c k.castSucc.val)
        (finiteBlindBranchValue v k.castSucc.val) (finiteBlindBranchValue a k.castSucc.val)
    simpa only [finiteBlindBranchValue_coe] using hcenter k
  have hs' (j : ℕ) (hj : j < N) :
      finiteBlindBranchValue a (j + 1) ≤ β * finiteBlindBranchValue a j := by
    let k : Fin N := ⟨j, hj⟩
    change finiteBlindBranchValue a k.succ.val ≤ β * finiteBlindBranchValue a k.castSucc.val
    simpa only [finiteBlindBranchValue_coe] using hshrink k
  have hy' : y ∈ centeredBlindSegment (finiteBlindBranchValue c N)
      (finiteBlindBranchValue v N) (finiteBlindBranchValue a N) := by
    change y ∈ centeredBlindSegment (finiteBlindBranchValue c (Fin.last N).val)
      (finiteBlindBranchValue v (Fin.last N).val) (finiteBlindBranchValue a (Fin.last N).val)
    simpa only [finiteBlindBranchValue_coe] using hy
  have h := shrinking_blind_descendant_mem_tube
    (finiteBlindBranchValue c) (finiteBlindBranchValue v) (finiteBlindBranchValue a)
    hβ hβhalf hV ha' hv' hc' hs' hy' i.val (Nat.le_of_lt_succ i.isLt)
  simpa only [finiteBlindBranchValue_coe] using h

/-- Actual finite good-ancestor compression with all geometric tube
hypotheses discharged. The relative thickness margin is reserved by
`V * β ≤ η / 2`; consequently every terminal point lies in every ancestor's
half-thickness tube, independently of the projection parameter. -/
theorem exists_uniform_blind_branch_compression
    {φ : ℝ × Plane → ℝ} {A : Set ℝ} (hA : IsCompact A)
    (q : Plane) {R : ℝ} (hR : 0 < R)
    (hφ : AnalyticOnNhd ℝ φ (A ×ˢ closedBall q R))
    {a b H ε : ℝ} (hab : a ≤ b) (hH : 0 < H) (hε : 0 < ε)
    (hhead : ∀ p ∈ A ×ˢ closedBall q R,
      scalarHeadDerivative φ p ≠ 0 ∧ |scalarHeadDerivative φ p| ≤ H)
    (hslope : ∀ p ∈ A ×ˢ closedBall q R, scalarGradientSlope φ p ∈ Icc a b) :
    ∃ N : ℕ, 0 < N ∧
      ∃ r > 0, ∃ η > 0, ∃ β > 0, ∃ ζ > 0,
        β ≤ 1 / 2 ∧
        max (max |a| |b|) 1 * β ≤ η / 2 ∧
        2 * ζ ≤ r ∧ 3 * ζ * (max (max |a| |b|) 1 + 2 * η) ≤ R / 2 ∧
        ∀ (c : Fin (N + 1) → Plane) (l : Fin (N + 1) → ℝ),
          (∀ i, c i ∈ ball q (R / 2)) →
          (∀ i, 0 < l i ∧ l i < ζ) →
          (∀ j : Fin N, c j.succ ∈ centeredBlindSegment
            (c j.castSucc) (-uniformSlopeGrid a b N j.castSucc, 1) (l j.castSucc)) →
          (∀ j : Fin N, l j.succ ≤ β * l j.castSucc) →
          ∀ y ∈ centeredBlindSegment (c (Fin.last N))
            (-uniformSlopeGrid a b N (Fin.last N), 1) (l (Fin.last N)),
            (∀ i, y ∈ thinSegmentTube (c i) (-uniformSlopeGrid a b N i, 1)
              (2 * l i) ((η / 2) * (2 * l i))) ∧
            (y ∈ ball q (R / 2) → ∀ t ∈ A, ∃ i : Fin (N + 1),
              volume ((fun z : Plane => φ (t, z)) ''
                thinSegmentTube (c i) (-uniformSlopeGrid a b N i, 1)
                  (2 * l i) (η * (2 * l i))) ≤ ENNReal.ofReal (ε * (2 * l i))) := by
  obtain ⟨N, hN, _hmesh, _hmono, _hfirst, _hlast, r, hr, η, hη, hcompress⟩ :=
    exists_uniformSlopeGrid_branch_compression hA (isCompact_closedBall q R)
      (convex_closedBall q R) hφ hab hH hε
  let V := max (max |a| |b|) 1
  have hV : 0 < V := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_right _ _)
  let β := min (1 / 2 : ℝ) (η / (2 * V))
  have hβ : 0 < β := lt_min (by norm_num) (div_pos hη (by positivity))
  have hβhalf : β ≤ 1 / 2 := min_le_left _ _
  have hβη : V * β ≤ η / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * V by positivity)).mp (min_le_right _ _ : β ≤ _)
    nlinarith
  let ζ := min (r / 2) (R / (6 * (V + 2 * η)))
  have hζ : 0 < ζ := lt_min (half_pos hr) (div_pos hR (by positivity))
  have hζr : 2 * ζ ≤ r := by have := min_le_left (r / 2) (R / (6 * (V + 2 * η))); linarith
  have hζR : 3 * ζ * (V + 2 * η) ≤ R / 2 := by
    have h := (le_div_iff₀ (show 0 < 6 * (V + 2 * η) by positivity)).mp
      (min_le_right _ _ : ζ ≤ _)
    nlinarith
  refine ⟨N, hN, r, hr, η, hη, β, hβ, ζ, hζ, hβhalf, hβη, hζr, hζR, ?_⟩
  intro c l hc hl hcenter hshrink y hy
  let v : Fin (N + 1) → Plane := fun i => (-uniformSlopeGrid a b N i, 1)
  have hv (i : Fin (N + 1)) : ‖v i‖ ≤ V :=
    norm_slopeDirection_le_of_mem_Icc (uniformSlopeGrid_mem_Icc hab hN i)
  have hhalf (i : Fin (N + 1)) :
      y ∈ thinSegmentTube (c i) (v i) (2 * l i) ((η / 2) * (2 * l i)) := by
    apply thinSegmentTube_mono_thickness (w := 2 * V * β * l i) ?_
      (shrinking_fin_blind_descendant_mem_tube c v l hβ.le hβhalf hV.le
        (fun j => (hl j).1.le) hv hcenter hshrink hy i)
    have h := mul_le_mul_of_nonneg_right hβη (hl i).1.le
    nlinarith
  have hfull (i : Fin (N + 1)) :
      y ∈ thinSegmentTube (c i) (v i) (2 * l i) (η * (2 * l i)) := by
    apply thinSegmentTube_mono_thickness _ (hhalf i)
    nlinarith [(hl i).1]
  refine ⟨hhalf, ?_⟩
  intro hyS t ht
  have hyK : y ∈ closedBall q R :=
    closedBall_subset_closedBall (half_le_self hR.le) (ball_subset_closedBall hyS)
  apply hcompress t ht y hyK (hhead (t, y) ⟨ht, hyK⟩).1
    (hhead (t, y) ⟨ht, hyK⟩).2 (hslope (t, y) ⟨ht, hyK⟩) c (fun i => 2 * l i)
  · intro i
    constructor
    · exact mul_nonneg (by norm_num) (hl i).1.le
    · have := (hl i).2; linarith
  · exact hfull
  · intro i
    have hsize : 3 * ((2 * l i) / 2 * V + η * (2 * l i)) ≤ R / 2 := by
      calc
        3 * ((2 * l i) / 2 * V + η * (2 * l i)) = 3 * l i * (V + 2 * η) := by ring
        _ ≤ 3 * ζ * (V + 2 * η) := by gcongr; exact (hl i).2.le
        _ ≤ R / 2 := hζR
    have hb := recentered_double_tube_subset_closedBall_of_half_radius
      (hfull i) (mul_nonneg (by norm_num) (hl i).1.le)
      (hv i) (ball_subset_closedBall (hc i)) hsize
    simpa only [show 2 * (η * (2 * l i)) = η * (2 * (2 * l i)) by ring] using hb

end PlanarNikodym
