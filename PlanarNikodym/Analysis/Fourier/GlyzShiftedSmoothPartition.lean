import PlanarNikodym.Analysis.Fourier.GlyzDyadicInput
import PlanarNikodym.Analysis.Fourier.GlyzTimeTranslation
import PlanarNikodym.Analysis.Localization.FiniteCutoffPartition
import Mathlib.Data.Nat.Prime.Basic

/-! A smooth time partition subordinate to five fixed translated dyadic
grids. The shifts are chosen before the depth, so no decoupling constant
can acquire a frequency dependence through the translated phase. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Manifold
namespace PlanarNikodym

def glyzSmoothGridShift : Fin 5 → ℝ := ![-1, 0, -5 / 3, -2 / 3, 1 / 3]

def glyzShiftedOpenCell (F : ℕ) (s : ℝ) (j : ℕ) : Set ℝ :=
  Ioo (s + glyzDyadicLeft F j) (s + glyzDyadicRight F j)

theorem glyz_two_pow_div_three_ne_int (F : ℕ) (z : ℤ) :
    (2 : ℝ) ^ F / 3 ≠ z := by
  intro h
  have heR : (2 : ℝ) ^ F = 3 * (z : ℝ) := by
    have hh := (div_eq_iff (by norm_num : (3 : ℝ) ≠ 0)).mp h
    nlinarith
  have heZ : (2 : ℤ) ^ F = 3 * z := by exact_mod_cast heR
  have hdZ : (3 : ℤ) ∣ (2 : ℤ) ^ F := ⟨z, heZ⟩
  have hdN : (3 : ℕ) ∣ (2 : ℕ) ^ F := by exact_mod_cast hdZ
  have hbad := Nat.prime_three.dvd_of_dvd_pow hdN
  norm_num at hbad

theorem glyz_unit_cell_or_boundary (F : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∃ j : Fin (2 ^ F), x ∈ Ioo (glyzDyadicLeft F j) (glyzDyadicRight F j)) ∨
      ∃ j : ℕ, x = glyzDyadicScale F * j := by
  have hδ := glyzDyadicScale_pos F
  have hc : glyzDyadicScale F * (2 : ℝ) ^ F = 1 := inv_mul_cancel₀ (by positivity)
  by_cases hx1 : x = 1
  · right
    refine ⟨2 ^ F, ?_⟩
    simpa only [hx1, Nat.cast_pow, Nat.cast_ofNat] using hc.symm
  · let j := ⌊(2 : ℝ) ^ F * x⌋₊
    have hy0 : 0 ≤ (2 : ℝ) ^ F * x := mul_nonneg (by positivity) hx.1
    have hj : j < 2 ^ F := by
      apply (Nat.floor_lt hy0).mpr
      push_cast
      calc
        (2 : ℝ) ^ F * x < (2 : ℝ) ^ F * 1 :=
          mul_lt_mul_of_pos_left (lt_of_le_of_ne hx.2 hx1) (by positivity)
        _ = _ := mul_one _
    have hl := Nat.floor_le hy0
    have hu := Nat.lt_floor_add_one ((2 : ℝ) ^ F * x)
    change (j : ℝ) ≤ _ at hl
    change _ < (j : ℝ) + 1 at hu
    have hl' := mul_le_mul_of_nonneg_left hl hδ.le
    have hu' := mul_lt_mul_of_pos_left hu hδ
    rw [← mul_assoc, hc, one_mul] at hl' hu'
    by_cases he : x = glyzDyadicScale F * j
    · exact Or.inr ⟨j, he⟩
    · left
      exact ⟨⟨j, hj⟩, lt_of_le_of_ne hl' (Ne.symm he), hu'⟩

theorem glyz_three_shifted_cells_cover (F : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ s ∈ ({0, 1 / 3, -2 / 3} : Set ℝ), ∃ j : Fin (2 ^ F), x ∈ glyzShiftedOpenCell F s j := by
  have hδ := glyzDyadicScale_pos F
  have hc : glyzDyadicScale F * (2 : ℝ) ^ F = 1 := inv_mul_cancel₀ (by positivity)
  rcases glyz_unit_cell_or_boundary F hx with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨0, by simp, j, by simpa only [glyzShiftedOpenCell, zero_add] using hj⟩
  · have hneq : x ≠ 1 / 3 := by
      intro he
      have hmul := congrArg (fun t : ℝ => t * (2 : ℝ) ^ F) hj
      rw [mul_right_comm, hc, one_mul, he] at hmul
      exact glyz_two_pow_div_three_ne_int F (j : ℤ) (by push_cast; nlinarith [hmul])
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have hy : x + 2 / 3 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith⟩
      rcases glyz_unit_cell_or_boundary F hy with ⟨l, hl⟩ | ⟨l, hl⟩
      · refine ⟨-2 / 3, by simp, l, ?_⟩
        change -2 / 3 + glyzDyadicLeft F l < x ∧ x < -2 / 3 + glyzDyadicRight F l
        constructor <;> linarith [hl.1, hl.2]
      · have hmulj := congrArg (fun t : ℝ => t * (2 : ℝ) ^ F) hj
        have hmull := congrArg (fun t : ℝ => t * (2 : ℝ) ^ F) hl
        rw [mul_right_comm, hc, one_mul] at hmulj hmull
        have he : (2 : ℝ) ^ F / 3 = ((2 : ℤ) ^ F + j - l : ℤ) := by
          push_cast
          nlinarith
        exact False.elim (glyz_two_pow_div_three_ne_int F _ he)
    · have hy : x - 1 / 3 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.2]⟩
      rcases glyz_unit_cell_or_boundary F hy with ⟨l, hl⟩ | ⟨l, hl⟩
      · refine ⟨1 / 3, by simp, l, ?_⟩
        change 1 / 3 + glyzDyadicLeft F l < x ∧ x < 1 / 3 + glyzDyadicRight F l
        constructor <;> linarith [hl.1, hl.2]
      · have hmulj := congrArg (fun t : ℝ => t * (2 : ℝ) ^ F) hj
        have hmull := congrArg (fun t : ℝ => t * (2 : ℝ) ^ F) hl
        rw [mul_right_comm, hc, one_mul] at hmulj hmull
        have he : (2 : ℝ) ^ F / 3 = ((j : ℤ) - l : ℤ) := by
          push_cast
          nlinarith
        exact False.elim (glyz_two_pow_div_three_ne_int F _ he)

theorem glyz_five_shifted_cells_cover (F : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ∃ s : Fin 5, ∃ j : Fin (2 ^ F), x ∈ glyzShiftedOpenCell F (glyzSmoothGridShift s) j := by
  by_cases hx0 : 0 ≤ x
  · obtain ⟨s, hs, j, hj⟩ := glyz_three_shifted_cells_cover F ⟨hx0, hx.2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨1, j, hj⟩
    · exact ⟨4, j, hj⟩
    · exact ⟨3, j, hj⟩
  · obtain ⟨s, hs, j, hj⟩ := glyz_three_shifted_cells_cover F
      (x := x + 1) ⟨by linarith [hx.1], by linarith⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨0, j, ?_⟩
      change -1 + glyzDyadicLeft F j < x ∧ x < -1 + glyzDyadicRight F j
      change 0 + glyzDyadicLeft F j < x + 1 ∧ x + 1 < 0 + glyzDyadicRight F j at hj
      constructor <;> linarith [hj.1, hj.2]
    · refine ⟨3, j, ?_⟩
      change -2 / 3 + glyzDyadicLeft F j < x ∧ x < -2 / 3 + glyzDyadicRight F j
      change 1 / 3 + glyzDyadicLeft F j < x + 1 ∧ x + 1 < 1 / 3 + glyzDyadicRight F j at hj
      constructor <;> linarith [hj.1, hj.2]
    · refine ⟨2, j, ?_⟩
      change -5 / 3 + glyzDyadicLeft F j < x ∧ x < -5 / 3 + glyzDyadicRight F j
      change -2 / 3 + glyzDyadicLeft F j < x + 1 ∧ x + 1 < -2 / 3 + glyzDyadicRight F j at hj
      constructor <;> linarith [hj.1, hj.2]

/-- Smooth pieces are supported strictly inside the corresponding
shifted cells, including at every grid boundary. -/
theorem exists_glyz_shifted_smooth_partition (F : ℕ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχ0 : ∀ t, 0 ≤ χ t)
    (hsχ : tsupport χ ⊆ Icc (-1 : ℝ) 1) :
    ∃ ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ,
      (∀ s j, ContDiff ℝ ∞ (ψ s j) ∧ HasCompactSupport (ψ s j) ∧
        tsupport (ψ s j) ⊆ tsupport χ ∧
        tsupport (ψ s j) ⊆ glyzShiftedOpenCell F (glyzSmoothGridShift s) j ∧
        ∀ t, 0 ≤ ψ s j t ∧ ψ s j t ≤ χ t) ∧
      ∀ t, ∑ s : Fin 5, ∑ j : Fin (2 ^ F), ψ s j t = χ t := by
  let U : (Fin 5 × Fin (2 ^ F)) → Set ℝ := fun i =>
    glyzShiftedOpenCell F (glyzSmoothGridShift i.1) i.2
  have hcover : tsupport χ ⊆ ⋃ i, U i := by
    intro t ht
    obtain ⟨s, j, hj⟩ := glyz_five_shifted_cells_cover F (hsχ ht)
    exact mem_iUnion.mpr ⟨(s, j), hj⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, ℝ)) (isClosed_tsupport χ) U (fun _ => isOpen_Ioo) hcover
  let ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ := fun s j t => χ t * ρ (s, j) t
  refine ⟨ψ, ?_, ?_⟩
  · intro s j
    exact ⟨hχ.mul (ρ (s, j)).contMDiff.contDiff, hcχ.mul_right,
      tsupport_mul_subset_left, tsupport_mul_subset_right.trans (hρ (s, j)),
      fun t => ⟨mul_nonneg (hχ0 t) (ρ.nonneg (s, j) t),
        (mul_le_mul_of_nonneg_left (ρ.le_one (s, j) t) (hχ0 t)).trans_eq (mul_one _)⟩⟩
  · intro t
    by_cases ht : t ∈ tsupport χ
    · have hsum : ∑ i : Fin 5 × Fin (2 ^ F), ρ i t = 1 :=
        ρ.sum_finsupport' t ht (Finset.subset_univ _)
      change ∑ s : Fin 5, ∑ j : Fin (2 ^ F), χ t * ρ (s, j) t = χ t
      rw [Fintype.sum_prod_type] at hsum
      simp_rw [← Finset.mul_sum]
      rw [hsum, mul_one]
    · have hz := image_eq_zero_of_notMem_tsupport ht
      simp only [ψ, hz, zero_mul, Finset.sum_const_zero]

theorem glyzDyadicInputSet_disjoint {F i j : ℕ} (hij : i ≠ j) :
    Disjoint (glyzDyadicInputSet F i) (glyzDyadicInputSet F j) := by
  apply Set.disjoint_left.mpr
  intro y hi hj
  change glyzDyadicScale F * i ≤ y.1 ∧ y.1 < glyzDyadicScale F * ((i : ℝ) + 1) at hi
  change glyzDyadicScale F * j ≤ y.1 ∧ y.1 < glyzDyadicScale F * ((j : ℝ) + 1) at hj
  have hδ := glyzDyadicScale_pos F
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    nlinarith [hi.1, hi.2, hj.1, hj.2]
  · have hh : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    nlinarith [hi.1, hi.2, hj.1, hj.2]

theorem glyzDyadicInput_finSum_supported (F : ℕ) (h : Fin (2 ^ F) → Plane → ℂ)
    (hs : ∀ j, Function.support (h j) ⊆ glyzDyadicInputSet F j)
    (j : Fin (2 ^ F)) :
    glyzDyadicInput F j (fun y => ∑ l : Fin (2 ^ F), h l y) = h j := by
  classical
  funext y
  by_cases hy : y ∈ glyzDyadicInputSet F j
  · rw [glyzDyadicInput, Set.indicator_of_mem hy]
    apply Finset.sum_eq_single j
    · intro l _ hlj
      by_contra hn
      exact Set.disjoint_left.mp (glyzDyadicInputSet_disjoint (Fin.val_ne_of_ne hlj))
        (hs l hn) hy
    · simp
  · rw [glyzDyadicInput, Set.indicator_of_notMem hy]
    exact (Function.notMem_support.mp (fun hn => hy (hs j hn))).symm

def glyzSmoothGridData (F : ℕ) (ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ)
    (s : Fin 5) (g : Plane → ℂ) (y : Plane) : ℂ :=
  ∑ j : Fin (2 ^ F), (ψ s j (y.1 + glyzSmoothGridShift s) : ℂ) *
    g (y.1 + glyzSmoothGridShift s, y.2)

/-- Each sharp dyadic restriction of a translated color is exactly its
specified smooth piece. No output norm monotonicity is used. -/
theorem glyzDyadicInput_smoothGridData (F : ℕ)
    (ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ)
    (hs : ∀ s j, tsupport (ψ s j) ⊆ glyzShiftedOpenCell F (glyzSmoothGridShift s) j)
    (s : Fin 5) (g : Plane → ℂ) (j : Fin (2 ^ F)) :
    glyzDyadicInput F j (glyzSmoothGridData F ψ s g) =
      fun y => (ψ s j (y.1 + glyzSmoothGridShift s) : ℂ) *
        g (y.1 + glyzSmoothGridShift s, y.2) := by
  apply glyzDyadicInput_finSum_supported
  intro l y hy
  have hn : ψ s l (y.1 + glyzSmoothGridShift s) ≠ 0 := by
    intro hz
    exact hy (by simp only [hz, Complex.ofReal_zero, zero_mul])
  have ht := hs s l (subset_tsupport _ hn)
  change glyzSmoothGridShift s + glyzDyadicLeft F l < y.1 + glyzSmoothGridShift s ∧
    y.1 + glyzSmoothGridShift s < glyzSmoothGridShift s + glyzDyadicRight F l at ht
  change glyzDyadicLeft F l ≤ y.1 ∧ y.1 < glyzDyadicRight F l
  constructor <;> linarith [ht.1, ht.2]

/-- Translated color data lie inside the standard root interval and
inherit exactly the original radial support. -/
theorem glyzSmoothGridData_support (F : ℕ)
    (ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ)
    (hs : ∀ s j, tsupport (ψ s j) ⊆ glyzShiftedOpenCell F (glyzSmoothGridShift s) j)
    (s : Fin 5) {g : Plane → ℂ} {J : Set ℝ}
    (hg : Function.support g ⊆ {y | y.2 ∈ J}) :
    Function.support (glyzSmoothGridData F ψ s g) ⊆ Ico (0 : ℝ) 1 ×ˢ J := by
  intro y hy
  have hex : ∃ j : Fin (2 ^ F), (ψ s j (y.1 + glyzSmoothGridShift s) : ℂ) *
      g (y.1 + glyzSmoothGridShift s, y.2) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (Finset.sum_eq_zero fun j _ => hn j)
  obtain ⟨j, hj⟩ := hex
  have hψ : ψ s j (y.1 + glyzSmoothGridShift s) ≠ 0 := by
    intro hz
    exact hj (by simp only [hz, Complex.ofReal_zero, zero_mul])
  have hrad : y.2 ∈ J := @hg (y.1 + glyzSmoothGridShift s, y.2)
    (right_ne_zero_of_mul hj)
  have ht := hs s j (subset_tsupport _ hψ)
  have hu := glyzDyadicInterval_subset_unit j.isLt
  have hyleft : glyzDyadicLeft F j ≤ y.1 := by
    change glyzSmoothGridShift s + glyzDyadicLeft F j < y.1 + glyzSmoothGridShift s ∧ _ at ht
    linarith [ht.1]
  have hyright : y.1 < glyzDyadicRight F j := by
    change _ ∧ y.1 + glyzSmoothGridShift s < glyzSmoothGridShift s + glyzDyadicRight F j at ht
    linarith [ht.2]
  have h01 := hu ⟨hyleft, hyright.le⟩
  have hright := hu (show glyzDyadicRight F j ∈ Icc (glyzDyadicLeft F j) (glyzDyadicRight F j) from
    ⟨(glyzDyadicLeft_lt_right F j).le, le_rfl⟩)
  exact ⟨⟨h01.1, hyright.trans_le hright.2⟩, hrad⟩

theorem integrable_glyzSmoothGridData (F : ℕ)
    (ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ)
    (hψ : ∀ s j, Continuous (ψ s j))
    (hrange : ∀ s j t, 0 ≤ ψ s j t ∧ ψ s j t ≤ 1)
    (s : Fin 5) {g : Plane → ℂ} (hg : Integrable g) :
    Integrable (glyzSmoothGridData F ψ s g) := by
  unfold glyzSmoothGridData
  apply integrable_finsetSum
  intro j _
  apply (integrable_glyzTimeTranslateInput hg (glyzSmoothGridShift s)).bdd_mul (c := 1)
    (Complex.continuous_ofReal.comp
      ((hψ s j).comp (continuous_fst.add continuous_const))).aestronglyMeasurable
  filter_upwards [] with y
  change ‖(ψ s j (y.1 + glyzSmoothGridShift s) : ℂ)‖ ≤ (1 : ℝ)
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hrange s j (y.1 + glyzSmoothGridShift s)).1] using
      (hrange s j (y.1 + glyzSmoothGridShift s)).2

theorem glyzSmoothGridData_eq_timeTranslate (F : ℕ)
    (ψ : Fin 5 → Fin (2 ^ F) → ℝ → ℝ) (s : Fin 5) (g : Plane → ℂ) :
    glyzSmoothGridData F ψ s g = glyzTimeTranslateInput
      (fun y => ((∑ j : Fin (2 ^ F), ψ s j y.1 : ℝ) : ℂ) * g y) (glyzSmoothGridShift s) := by
  funext y
  simp only [glyzSmoothGridData, glyzTimeTranslateInput, Complex.ofReal_sum, Finset.sum_mul]

theorem glyzShiftedOpenCell_length (F j : ℕ) (s : ℝ) :
    (s + glyzDyadicRight F j) - (s + glyzDyadicLeft F j) = glyzDyadicScale F := by
  rw [add_sub_add_left_eq_sub, glyzDyadicInterval_length]

/-- The original amplitude's compact time support can be localized by
one cutoff chosen before all frequencies and all partition depths. -/
theorem exists_glyz_smooth_time_cutoff {K : Set ℝ} (hK : IsCompact K)
    (hKS : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ tsupport χ ⊆ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ K, χ t = 1 := by
  obtain ⟨χ, V, hχ, hcχ, hr, _, hKV, hV1, hs⟩ :=
    exists_compact_smooth_cutoff hK isOpen_Ioo hKS
  exact ⟨χ, hχ, hcχ, hr, hs, fun t ht => hV1 t (hKV ht)⟩

end PlanarNikodym
