import PlanarNikodym.Projection.UniformBlindBranchCompression
import PlanarNikodym.Projection.DyadicBlindTreeBudget
import PlanarNikodym.Projection.ThickenedBlindTrace

/-! A uniform finite fan constructed by actual slope-grid replacements.

The directions, refinement trace, compressible ancestor on every branch,
and total length bound are all constructed here. A subsequent common
positive thickening retains these bounds and gives interior coverage.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped Topology BigOperators ENNReal

namespace PlanarNikodym

/-- The equispaced blind directions, held constant beyond the last level. -/
def uniformBlindDirection (a b : ℝ) (N : ℕ) : ℕ → Plane :=
  finiteBlindBranchValue (fun i : Fin (N + 1) => (-uniformSlopeGrid a b N i, 1))

@[simp] theorem uniformBlindDirection_coe (a b : ℝ) (N : ℕ) (i : Fin (N + 1)) :
    uniformBlindDirection a b N i.val = (-uniformSlopeGrid a b N i, 1) :=
  finiteBlindBranchValue_coe _ i

@[simp] theorem uniformBlindDirection_zero (a b : ℝ) (N : ℕ) :
    uniformBlindDirection a b N 0 = (-a, 1) := by
  simpa using uniformBlindDirection_coe a b N 0

theorem uniformBlindDirection_ne_zero (a b : ℝ) (N k : ℕ) :
    uniformBlindDirection a b N k ≠ 0 := by
  intro h
  have hs := congrArg Prod.snd h
  norm_num [uniformBlindDirection, finiteBlindBranchValue] at hs

theorem uniformBlindDirection_norm_le {a b : ℝ} (hab : a ≤ b)
    {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ‖uniformBlindDirection a b N k‖ ≤ max (max |a| |b|) 1 :=
  norm_slopeDirection_le_of_mem_Icc
    (uniformSlopeGrid_mem_Icc hab hN
      ⟨min k N, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)

theorem uniformBlindDirection_step {a b : ℝ} (hab : a ≤ b)
    (N k : ℕ) (hk : k < N) :
    ‖uniformBlindDirection a b N (k + 1) - uniformBlindDirection a b N k‖ =
      (b - a) / (N : ℝ) := by
  let i : Fin N := ⟨k, hk⟩
  change ‖uniformBlindDirection a b N i.succ.val -
    uniformBlindDirection a b N i.castSucc.val‖ = _
  rw [uniformBlindDirection_coe, uniformBlindDirection_coe]
  have hnonneg : 0 ≤ (b - a) / (N : ℝ) :=
    div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  have he : -uniformSlopeGrid a b N i.succ - -uniformSlopeGrid a b N i.castSucc =
      -((b - a) / (N : ℝ)) := by
    have := uniformSlopeGrid_step a b N i
    linarith
  simp [Prod.norm_def, he, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab),
    max_eq_left hnonneg]

/-- A real finite refinement trace, with a compressible actual ancestor
for every terminal branch and every parameter in the compact family.
The exponential length bound depends only on the slope interval. -/
theorem exists_uniform_small_projection_trace
    {φ : ℝ × Plane → ℝ} {A : Set ℝ} (hA : IsCompact A)
    (q : Plane) {R : ℝ} (hR : 0 < R)
    (hφ : AnalyticOnNhd ℝ φ (A ×ˢ closedBall q R))
    {a b H ρ : ℝ} (hab : a ≤ b) (hH : 0 < H) (hρ : 0 < ρ)
    (hhead : ∀ p ∈ A ×ˢ closedBall q R,
      scalarHeadDerivative φ p ≠ 0 ∧ |scalarHeadDerivative φ p| ≤ H)
    (hslope : ∀ p ∈ A ×ˢ closedBall q R, scalarGradientSlope φ p ∈ Icc a b)
    {ι : Type*} (f : ι → Plane → ℝ) (P₀ : FiniteBlindFamily Plane)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ i z, z ∈ ball q (R / 2) → DifferentiableAt ℝ (f i) z)
    (hbound : ∀ i z, z ∈ ball q (R / 2) → ‖fderiv ℝ (f i) z‖ ≤ M)
    (hd : ∀ s ∈ Icc a b, ∀ i z, z ∈ ball q (R / 2) →
      m ≤ fderiv ℝ (f i) z (-s, 1))
    {W : Set Plane} (hW : IsOpen W) (hWS : W ⊆ ball q (R / 2))
    (hP : ∀ i, 0 < P₀.halfLength i) (hPW : P₀.carrier (-a, 1) ⊆ W) :
    ∃ N : ℕ, 0 < N ∧ ∃ η > 0, ∃ β > 0,
      ∃ Q : FiniteBlindFamily Plane,
      ∃ trace : DyadicBlindTrace P₀ (uniformBlindDirection a b N)
          (fun _ => 1 + M / m * ((b - a) / (N : ℝ))) N Q,
        trace.Shrinks β ∧ β ≤ 1 / 2 ∧ max (max |a| |b|) 1 * β ≤ η / 2 ∧
        Q.carrier (uniformBlindDirection a b N N) ⊆ W ∧
        Q.budget ≤ P₀.budget * Real.exp (M / m * (b - a)) ∧
        (∀ i, f i '' P₀.carrier (-a, 1) ⊆
          f i '' Q.carrier (uniformBlindDirection a b N N)) ∧
        ∀ t ∈ A, trace.EveryBranchMarked (fun u =>
          volume ((fun z : Plane => φ (t, z)) ''
            thinSegmentTube (trace.nodeCenter u)
              (uniformBlindDirection a b N (trace.nodeLevel u))
              (2 * trace.nodeHalfLength u) (η * (2 * trace.nodeHalfLength u))) ≤
            ENNReal.ofReal (ρ * (2 * trace.nodeHalfLength u))) := by
  classical
  obtain ⟨N, hN, r, _hr, η, hη, β, hβ, ζ, hζ,
      hβhalf, hβη, _hζr, _hζR, hcompress⟩ :=
    exists_uniform_blind_branch_compression hA q hR hφ hab hH hρ hhead hslope
  let v := uniformBlindDirection a b N
  let δ : ℕ → ℝ := fun _ => (b - a) / (N : ℝ)
  have hδ : ∀ k < N, 0 ≤ δ k :=
    fun _ _ => div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  have hΛ : ∀ k < N, 0 < 1 + M / m * δ k := by
    intro k hk
    have := mul_nonneg (div_nonneg hM hm.le) (hδ k hk)
    linarith
  have hvzero : v 0 = (-a, 1) := uniformBlindDirection_zero a b N
  obtain ⟨d, hdpos, hdbuffer⟩ :=
    (P₀.isCompact_carrier (-a, 1)).exists_thickening_subset_open hW hPW
  have hPS : P₀.carrier (v 0) ⊆ ball q (R / 2) := by
    rw [hvzero]
    exact hPW.trans hWS
  have hvd : ∀ k ≤ N, ∀ i z, z ∈ ball q (R / 2) →
      m ≤ fderiv ℝ (f i) z (v k) := by
    intro k hk i z hz
    let j : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    change m ≤ fderiv ℝ (f i) z (uniformBlindDirection a b N j.val)
    rw [uniformBlindDirection_coe]
    exact hd _ (uniformSlopeGrid_mem_Icc hab hN j) i z hz
  obtain ⟨Q, ⟨trace, hdomain, hshrink, hshort⟩, hpositive, _hQS,
      hclose, hbudget, hcover⟩ :=
    exists_iterated_blind_replacement_shrinking f P₀ v δ isOpen_ball
      (convex_ball q (R / 2)) hP hPS hm hM hf hbound N
      (fun k _ => uniformBlindDirection_ne_zero a b N k) hvd hδ
      (fun k hk => (uniformBlindDirection_step hab N k hk).le)
      β d ζ hβ hdpos hζ
  have hQW : Q.carrier (v N) ⊆ W := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hclose x hx
    rw [hvzero] at hy
    exact hdbuffer (mem_thickening_iff.mpr ⟨y, hy, hxy⟩)
  have hPbudget : 0 ≤ P₀.budget :=
    Finset.sum_nonneg (fun i _ => (hP i).le)
  have hsum : (∑ k ∈ Finset.range N, δ k) = b - a := by
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [δ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hB : Q.budget ≤ P₀.budget * Real.exp (M / m * (b - a)) := by
    rw [hbudget]
    apply mul_le_mul_of_nonneg_left _ hPbudget
    simpa only [hsum] using blindExpansionProduct_le_exp
      (M / m) (div_nonneg hM hm.le) δ N hδ
  refine ⟨N, hN, η, hη, β, hβ, Q, trace, hshrink, hβhalf, hβη, hQW, hB, ?_, ?_⟩
  · simpa only [hvzero] using hcover
  · intro t ht
    apply trace.everyBranchMarked_of_ancestor
    intro j
    let c : Fin (N + 1) → Plane := fun i => trace.branchCenter j i.val
    let l : Fin (N + 1) → ℝ := fun i => trace.branchHalfLength j i.val
    have hl (i : Fin (N + 1)) : 0 < l i ∧ l i < ζ :=
      ⟨trace.branch_halfLength_pos hP hΛ j i.val (Nat.le_of_lt_succ i.isLt),
        trace.branch_halfLength_lt hshort j i.val (Nat.le_of_lt_succ i.isLt)⟩
    have hc (i : Fin (N + 1)) : c i ∈ ball q (R / 2) := by
      apply trace.branch_segment_subset_domain hdomain j i.val (Nat.le_of_lt_succ i.isLt)
      simpa only [zero_smul, add_zero] using
        mem_centeredBlindSegment (c i) (v i.val) (t := 0) (by simpa using (hl i).1.le)
    have hparents (i : Fin N) : c i.succ ∈ centeredBlindSegment
        (c i.castSucc) (-uniformSlopeGrid a b N i.castSucc, 1) (l i.castSucc) := by
      have h := trace.branch_center_mem_parent hP hΛ j i.val i.isLt
      change c i.succ ∈ centeredBlindSegment (c i.castSucc)
        (uniformBlindDirection a b N i.castSucc.val) (l i.castSucc) at h
      simpa only [uniformBlindDirection_coe] using h
    have hshrinks (i : Fin N) : l i.succ ≤ β * l i.castSucc :=
      trace.branch_halfLength_shrinks hshrink j i.val i.isLt
    have hy : Q.center j ∈ centeredBlindSegment (c (Fin.last N))
        (-uniformSlopeGrid a b N (Fin.last N), 1) (l (Fin.last N)) := by
      simpa only [c, l, Fin.val_last, trace.branchCenter_last, trace.branchHalfLength_last,
        zero_smul, add_zero] using
          mem_centeredBlindSegment (Q.center j)
            (-uniformSlopeGrid a b N (Fin.last N), 1) (t := 0)
            (by simpa using (hpositive j).1.le)
    have hyS : Q.center j ∈ ball q (R / 2) := by
      simpa only [c, Fin.val_last, trace.branchCenter_last] using hc (Fin.last N)
    obtain ⟨i, hi⟩ := (hcompress c l hc hl hparents hshrinks (Q.center j) hy).2 hyS t ht
    refine ⟨i.val, Nat.le_of_lt_succ i.isLt, ?_⟩
    simpa only [trace.nodeCenter_ancestorNode, trace.nodeHalfLength_ancestorNode,
      trace.nodeLevel_ancestorNode j i.val (Nat.le_of_lt_succ i.isLt),
      uniformBlindDirection_coe, c, l] using hi

/-- The actual compact uniform fan. Its positive thickening gives interior
coverage for the entire preserved family while all projections in the
compact analytic family have the prescribed arbitrarily small measure. -/
theorem exists_uniform_small_projection_fan
    {φ : ℝ × Plane → ℝ} {A : Set ℝ} (hA : IsCompact A)
    (q : Plane) {R : ℝ} (hR : 0 < R)
    (hφ : AnalyticOnNhd ℝ φ (A ×ˢ closedBall q R))
    {a b H ε : ℝ} (hab : a ≤ b) (hH : 0 < H) (hε : 0 < ε)
    (hhead : ∀ p ∈ A ×ˢ closedBall q R,
      scalarHeadDerivative φ p ≠ 0 ∧ |scalarHeadDerivative φ p| ≤ H)
    (hslope : ∀ p ∈ A ×ˢ closedBall q R, scalarGradientSlope φ p ∈ Icc a b)
    {ι : Type*} (f : ι → Plane → ℝ) (P₀ : FiniteBlindFamily Plane)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ i z, z ∈ ball q (R / 2) → DifferentiableAt ℝ (f i) z)
    (hbound : ∀ i z, z ∈ ball q (R / 2) → ‖fderiv ℝ (f i) z‖ ≤ M)
    (hd : ∀ s ∈ Icc a b, ∀ i z, z ∈ ball q (R / 2) →
      m ≤ fderiv ℝ (f i) z (-s, 1))
    {W : Set Plane} (hW : IsOpen W) (hWS : W ⊆ ball q (R / 2))
    (hP : ∀ i, 0 < P₀.halfLength i) (hPW : P₀.carrier (-a, 1) ⊆ W) :
    ∃ L : Set Plane, IsCompact L ∧ L ⊆ W ∧
      (∀ i, f i '' P₀.carrier (-a, 1) ⊆ f i '' interior L) ∧
      ∀ t ∈ A, volume ((fun z : Plane => φ (t, z)) '' L) ≤ ENNReal.ofReal ε := by
  classical
  let B := P₀.budget * Real.exp (M / m * (b - a))
  let D := max B 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let ρ := ε / (2 * D)
  have hρ : 0 < ρ := div_pos hε (mul_pos (by norm_num) hD)
  obtain ⟨N, hN, η, hη, β, hβ, Q, trace, hshrink,
      hβhalf, hβη, hQW, hbudget, hcover, hbranch⟩ :=
    exists_uniform_small_projection_trace hA q hR hφ hab hH hρ hhead hslope
      f P₀ hm hM hf hbound hd hW hWS hP hPW
  let good : ℝ → trace.Node → Prop := fun t u =>
    volume ((fun z : Plane => φ (t, z)) '' trace.fullNodeTube η u) ≤
      ENNReal.ofReal (ρ * (2 * trace.nodeHalfLength u))
  have hΛ : ∀ k < N, 1 ≤ 1 + M / m * ((b - a) / (N : ℝ)) := by
    intro _ _
    have := mul_nonneg (div_nonneg hM hm.le)
      (div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N))
    linarith
  obtain ⟨d, _hd, hcompact, hinterior, hinside, hmeasure⟩ :=
    trace.exists_uniform_thickened_projection_bound hP hΛ
      (fun k _ => uniformBlindDirection_ne_zero a b N k)
      hshrink hβ.le hβhalf
      (le_trans zero_le_one (le_max_right _ _))
      (fun k _ => uniformBlindDirection_norm_le hab hN k) hη hβη hW hQW
      (fun t z => φ (t, z)) A (ENNReal.ofReal ρ) good
      (fun _ _ _ hu => by simpa only [good, ENNReal.ofReal_mul hρ.le] using hu)
      hbranch
  refine ⟨cthickening d (Q.carrier (uniformBlindDirection a b N N)),
    hcompact, hinside, ?_, ?_⟩
  · intro i
    exact (hcover i).trans (image_mono hinterior)
  · intro t ht
    apply (hmeasure t ht).trans
    rw [← ENNReal.ofReal_mul hρ.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      ρ * (2 * Q.budget) ≤ ρ * (2 * D) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbudget.trans (le_max_left _ _)) (by norm_num)) hρ.le
      _ = ε := by dsimp only [ρ]; exact div_mul_cancel₀ _ (ne_of_gt (by positivity))

/-- Single initial segment form used by the local replacement and nested
compact construction. The half-length is the parameter half-length. -/
theorem exists_uniform_small_projection_segment_fan
    {φ : ℝ × Plane → ℝ} {A : Set ℝ} (hA : IsCompact A)
    (q : Plane) {R : ℝ} (hR : 0 < R)
    (hφ : AnalyticOnNhd ℝ φ (A ×ˢ closedBall q R))
    {a b H ε : ℝ} (hab : a ≤ b) (hH : 0 < H) (hε : 0 < ε)
    (hhead : ∀ p ∈ A ×ˢ closedBall q R,
      scalarHeadDerivative φ p ≠ 0 ∧ |scalarHeadDerivative φ p| ≤ H)
    (hslope : ∀ p ∈ A ×ˢ closedBall q R, scalarGradientSlope φ p ∈ Icc a b)
    {ι : Type*} (f : ι → Plane → ℝ) {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hf : ∀ i z, z ∈ ball q (R / 2) → DifferentiableAt ℝ (f i) z)
    (hbound : ∀ i z, z ∈ ball q (R / 2) → ‖fderiv ℝ (f i) z‖ ≤ M)
    (hd : ∀ s ∈ Icc a b, ∀ i z, z ∈ ball q (R / 2) →
      m ≤ fderiv ℝ (f i) z (-s, 1))
    {W : Set Plane} (hW : IsOpen W) (hWS : W ⊆ ball q (R / 2))
    (c : Plane) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hseg : centeredBlindSegment c (-a, 1) ℓ ⊆ W) :
    ∃ L : Set Plane, IsCompact L ∧ L ⊆ W ∧
      (∀ i, f i '' centeredBlindSegment c (-a, 1) ℓ ⊆ f i '' interior L) ∧
      ∀ t ∈ A, volume ((fun z : Plane => φ (t, z)) '' L) ≤ ENNReal.ofReal ε := by
  simpa only [FiniteBlindFamily.carrier_singleton] using
    exists_uniform_small_projection_fan hA q hR hφ hab hH hε hhead hslope
      f (FiniteBlindFamily.singleton c ℓ) hm hM hf hbound hd hW hWS
      (fun _ => hℓ) (by simpa only [FiniteBlindFamily.carrier_singleton] using hseg)

end PlanarNikodym
