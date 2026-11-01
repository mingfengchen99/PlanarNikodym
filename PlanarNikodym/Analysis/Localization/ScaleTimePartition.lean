import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

/-! An explicit smooth time partition at every positive scale. Its
derivative constants are those of one fixed compactly supported window;
they do not depend on the scale, the translate, or the number of slices. -/

noncomputable section
open Set
open scoped ContDiff Classical

namespace PlanarNikodym

/-- A nonnegative smooth window whose integer translates telescope. -/
def timePartitionWindow (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem contDiff_timePartitionWindow : ContDiff ℝ ∞ timePartitionWindow :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem timePartitionWindow_nonneg (x : ℝ) : 0 ≤ timePartitionWindow x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem timePartitionWindow_le_one (x : ℝ) : timePartitionWindow x ≤ 1 := by
  exact (sub_le_self _ (Real.smoothTransition.nonneg x)).trans
    (Real.smoothTransition.le_one _)

theorem timePartitionWindow_eq_zero {x : ℝ} (hx : x ≤ -1 ∨ 1 ≤ x) :
    timePartitionWindow x = 0 := by
  rcases hx with hx | hx
  · rw [timePartitionWindow, Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]
  · rw [timePartitionWindow, Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le hx, sub_self]

theorem tsupport_timePartitionWindow_subset : tsupport timePartitionWindow ⊆ Icc (-1) 1 := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hn
  exact hx (timePartitionWindow_eq_zero (by
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · exact Or.inl hn.le
    · exact Or.inr hn.le))

theorem hasCompactSupport_timePartitionWindow : HasCompactSupport timePartitionWindow :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) tsupport_timePartitionWindow_subset

/-- A translate of the fixed window, on the time scale `δ`. -/
def scaleTimeCutoff (a δ : ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  timePartitionWindow ((t - a) / δ - i)

theorem contDiff_scaleTimeCutoff (a δ : ℝ) (i : ℕ) :
    ContDiff ℝ ∞ (scaleTimeCutoff a δ i) :=
  contDiff_timePartitionWindow.comp
    (((contDiff_id.sub contDiff_const).div_const δ).sub contDiff_const)

theorem scaleTimeCutoff_nonneg (a δ t : ℝ) (i : ℕ) :
    0 ≤ scaleTimeCutoff a δ i t := timePartitionWindow_nonneg _

theorem scaleTimeCutoff_le_one (a δ t : ℝ) (i : ℕ) :
    scaleTimeCutoff a δ i t ≤ 1 := timePartitionWindow_le_one _

/-- The closed support has radius exactly at most one time scale. -/
theorem tsupport_scaleTimeCutoff_subset (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) :
    tsupport (scaleTimeCutoff a δ i) ⊆
      Icc (a + ((i : ℝ) - 1) * δ) (a + ((i : ℝ) + 1) * δ) := by
  have hcont : Continuous (fun t : ℝ => (t - a) / δ - i) := by fun_prop
  have hs := tsupport_comp_subset_preimage timePartitionWindow hcont
  intro t ht
  have hw := tsupport_timePartitionWindow_subset (hs ht)
  change -1 ≤ (t - a) / δ - i ∧ (t - a) / δ - i ≤ 1 at hw
  have hlo : ((i : ℝ) - 1) * δ ≤ t - a :=
    (le_div_iff₀ hδ).mp (by linarith [hw.1])
  have hhi : t - a ≤ ((i : ℝ) + 1) * δ :=
    (div_le_iff₀ hδ).mp (by linarith [hw.2])
  exact ⟨by linarith, by linarith⟩

theorem hasCompactSupport_scaleTimeCutoff (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) :
    HasCompactSupport (scaleTimeCutoff a δ i) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_scaleTimeCutoff_subset a hδ i)

/-- At most three closed supports meet at any time, independently of the
scale and the total number of intervals. -/
theorem scaleTimeCutoff_overlap_le_three (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) (t : ℝ) :
    ((Finset.range N).filter (fun i => t ∈ tsupport (scaleTimeCutoff a δ i))).card ≤ 3 := by
  classical
  let x : ℝ := (t - a) / δ
  let J : Finset ℤ := Finset.Icc (⌊x⌋ - 1) (⌊x⌋ + 1)
  have hmap : Set.MapsTo (fun i : ℕ => (i : ℤ))
      (↑((Finset.range N).filter (fun i => t ∈ tsupport (scaleTimeCutoff a δ i))) : Set ℕ)
      (↑J : Set ℤ) := by
    intro i hi
    have hs := tsupport_scaleTimeCutoff_subset a hδ i (Finset.mem_filter.mp hi).2
    have hi₁ : (i : ℝ) - 1 ≤ x := (le_div_iff₀ hδ).mpr (by linarith [hs.1])
    have hi₂ : x ≤ (i : ℝ) + 1 := (div_le_iff₀ hδ).mpr (by linarith [hs.2])
    have hf₁ := Int.floor_le x
    have hf₂ := Int.lt_floor_add_one x
    have hlow : ((⌊x⌋ : ℤ) : ℝ) - 1 ≤ (i : ℝ) := by linarith
    have hhigh : (i : ℝ) < ((⌊x⌋ : ℤ) : ℝ) + 2 := by linarith
    have hlow' : ⌊x⌋ - 1 ≤ (i : ℤ) := by exact_mod_cast hlow
    have hhigh' : (i : ℤ) < ⌊x⌋ + 2 := by exact_mod_cast hhigh
    change (i : ℤ) ∈ J
    exact Finset.mem_Icc.mpr ⟨hlow', by omega⟩
  have hc := Finset.card_le_card_of_injOn (fun i : ℕ => (i : ℤ)) hmap
    (fun _ _ _ _ h => Int.ofNat_injective h)
  have hJ : J.card = 3 := by
    dsimp only [J]
    rw [Int.card_Icc]
    rw [show ⌊x⌋ + 1 + 1 - (⌊x⌋ - 1) = (3 : ℤ) by ring]
    rfl
  exact hc.trans_eq hJ

/-- Exact finite telescoping, including the two boundary terms. -/
theorem sum_scaleTimeCutoff (a δ t : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t =
      Real.smoothTransition ((t - a) / δ + 1) -
        Real.smoothTransition ((t - a) / δ + 1 - N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [scaleTimeCutoff, timePartitionWindow, Nat.cast_add, Nat.cast_one]
    have he : (t - a) / δ - (N : ℝ) + 1 = (t - a) / δ + 1 - N := by ring
    have he' : (t - a) / δ + 1 - ((N : ℝ) + 1) = (t - a) / δ - N := by ring
    rw [he, he']
    ring

theorem sum_scaleTimeCutoff_eq_one (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    {t : ℝ} (ht : t ∈ Icc a (a + ((N : ℝ) - 1) * δ)) :
    ∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t = 1 := by
  rw [sum_scaleTimeCutoff]
  have hlo : 0 ≤ (t - a) / δ := div_nonneg (sub_nonneg.mpr ht.1) hδ.le
  have hhi : (t - a) / δ ≤ (N : ℝ) - 1 :=
    (div_le_iff₀ hδ).mpr (by linarith [ht.2])
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

/-- Every bounded interval is covered at every positive scale. -/
theorem exists_scaleTimeCutoff_partition (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ t ∈ Icc a b,
      ∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t = 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨n + 1, ?_⟩
  intro t ht
  apply sum_scaleTimeCutoff_eq_one a hδ
  refine ⟨ht.1, ?_⟩
  have hbn : b - a < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  linarith [ht.2]

/-- Derivatives of the single window have genuine global bounds. -/
theorem exists_timePartitionWindow_deriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv m timePartitionWindow x| ≤ C := by
  have hc : HasCompactSupport (iteratedDeriv m timePartitionWindow) := by
    induction m with
    | zero => exact hasCompactSupport_timePartitionWindow
    | succ m ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hcont := (contDiff_infty.mp contDiff_timePartitionWindow m).continuous_iteratedDeriv' m
  obtain ⟨x, hx⟩ := hcont.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  exact ⟨‖iteratedDeriv m timePartitionWindow x‖, norm_nonneg _, by
    intro y
    simpa only [Real.norm_eq_abs] using hx y⟩

/-- Exact all-order chain rule for the translated and dilated window. -/
theorem iteratedDeriv_scaleTimeCutoff (a δ : ℝ) (i m : ℕ) (t : ℝ) :
    iteratedDeriv m (scaleTimeCutoff a δ i) t =
      (δ⁻¹) ^ m * iteratedDeriv m timePartitionWindow ((t - a) / δ - i) := by
  have he : scaleTimeCutoff a δ i =
      fun t => (fun y => (fun x => timePartitionWindow (x - i)) (δ⁻¹ * y)) (t - a) := by
    funext t
    simp only [scaleTimeCutoff, div_eq_mul_inv, mul_comm]
  rw [he, iteratedDeriv_comp_sub_const m
    (fun y => timePartitionWindow (δ⁻¹ * y - i)) a]
  dsimp only
  have hh : ContDiff ℝ m (fun x : ℝ => timePartitionWindow (x - i)) :=
    contDiff_infty.mp (contDiff_timePartitionWindow.comp
      (contDiff_id.sub (contDiff_const (c := (i : ℝ))))) m
  rw [congrFun (iteratedDeriv_comp_const_mul hh δ⁻¹) (t - a)]
  rw [iteratedDeriv_comp_sub_const m timePartitionWindow (i : ℝ)]
  simp only [div_eq_mul_inv, mul_comm]

/-- One derivative constant works for every translate and every positive
scale, with the sharp scale factor `δ⁻ᵐ`. -/
theorem exists_uniform_scaleTimeCutoff_deriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a δ t : ℝ) (i : ℕ), 0 < δ →
      |iteratedDeriv m (scaleTimeCutoff a δ i) t| ≤ C * (δ⁻¹) ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_timePartitionWindow_deriv_bound m
  refine ⟨C, hC, ?_⟩
  intro a δ t i hδ
  rw [iteratedDeriv_scaleTimeCutoff, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hδ)]
  exact (mul_le_mul_of_nonneg_left (hbound _) (by positivity)).trans_eq (mul_comm _ _)

end PlanarNikodym
