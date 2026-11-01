import PlanarNikodym.Analysis.Localization.AnalyticCutoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! An actual signed smooth cutoff is a difference of two nonnegative
smooth compact cutoffs in the same prescribed open set. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym

/-- The support enlargement is confined to `O`; the two cutoffs and their
constants are chosen solely from the original cutoff and that open set. -/
theorem exists_scalarJet_signed_cutoff_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {O : Set E} (hO : IsOpen O) (hs : tsupport χ ⊆ O) :
    ∃ χp χn : E → ℝ,
      ContDiff ℝ ∞ χp ∧ HasCompactSupport χp ∧ tsupport χp ⊆ O ∧
      (∀ x, 0 ≤ χp x) ∧
      ContDiff ℝ ∞ χn ∧ HasCompactSupport χn ∧ tsupport χn ⊆ O ∧
      (∀ x, 0 ≤ χn x) ∧ ∀ x, χ x = χp x - χn x := by
  obtain ⟨η, U, hη, hcη, hη01, _, hKU, hη1, hsη⟩ :=
    exists_compact_smooth_cutoff hc.isCompact hO hs
  let S : SchwartzMap E ℝ := hc.toSchwartzMap hχ
  let B := SchwartzMap.seminorm ℝ 0 0 S
  have hB : 0 ≤ B := apply_nonneg _ _
  let χn : E → ℝ := fun x => B * η x
  have hn : ContDiff ℝ ∞ χn := contDiff_const.mul hη
  have hnc : HasCompactSupport χn := hcη.mul_left
  have hns : tsupport χn ⊆ O := tsupport_mul_subset_right.trans hsη
  have hn0 (x : E) : 0 ≤ χn x := mul_nonneg hB (hη01 x).1
  refine ⟨fun x => χn x + χ x, χn, hn.add hχ, hnc.add hc,
    (tsupport_add _ _).trans (union_subset hns hs), ?_, hn, hnc, hns, hn0, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport χ
    · have hbound : |χ x| ≤ B := by simpa [S, Real.norm_eq_abs] using S.norm_le_seminorm ℝ x
      have hηx := hη1 x (hKU hx)
      dsimp [χn]
      rw [hηx, mul_one]
      linarith [neg_abs_le (χ x)]
    · change 0 ≤ χn x + χ x
      rw [image_eq_zero_of_notMem_tsupport hx, add_zero]
      exact hn0 x
  · intro x
    ring

end PlanarNikodym
