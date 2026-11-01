import PlanarNikodym.Analysis.Fourier.GlyzShiftedSmoothPartition
import Mathlib.Data.Nat.ModEq

/-! A depth-independent interior margin for the fixed translated grids,
and a bounded residue coloring for exact standard time intervals. -/
noncomputable section
open Set
open scoped BigOperators
namespace PlanarNikodym

theorem glyz_two_pow_div_three_distance (F : ℕ) (z : ℤ) :
    (1 / 3 : ℝ) ≤ |(2 : ℝ) ^ F / 3 - z| := by
  have hn : (2 : ℤ) ^ F - 3 * z ≠ 0 := by
    intro hz
    have he : (2 : ℝ) ^ F - 3 * (z : ℝ) = 0 := by exact_mod_cast hz
    apply glyz_two_pow_div_three_ne_int F z
    linarith
  have h := Int.one_le_abs hn
  have hR : (1 : ℝ) ≤ |(2 : ℝ) ^ F - 3 * (z : ℝ)| := by exact_mod_cast h
  have he : |(2 : ℝ) ^ F / 3 - z| = |(2 : ℝ) ^ F - 3 * (z : ℝ)| / 3 := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 3), ← abs_div]
    congr 1
    ring
  rw [he]
  linarith

theorem glyz_dyadic_boundary_separation (F : ℕ) (u v : ℤ) :
    glyzDyadicScale F / 3 ≤
      |glyzDyadicScale F * u - (1 / 3 + glyzDyadicScale F * v)| := by
  have hδ := glyzDyadicScale_pos F
  have hc : glyzDyadicScale F * (2 : ℝ) ^ F = 1 := inv_mul_cancel₀ (by positivity)
  have hd := glyz_two_pow_div_three_distance F (u - v)
  have hh := mul_le_mul_of_nonneg_left hd hδ.le
  have he : glyzDyadicScale F * ((2 : ℝ) ^ F / 3 - (u - v : ℤ)) =
      -(glyzDyadicScale F * u - (1 / 3 + glyzDyadicScale F * v)) := by
    push_cast
    calc
      _ = glyzDyadicScale F * (2 : ℝ) ^ F / 3 - glyzDyadicScale F * ((u : ℝ) - v) := by ring
      _ = _ := by rw [hc]; ring
  rw [← abs_of_pos hδ, ← abs_mul, he, abs_neg] at hh
  simpa only [abs_of_pos hδ, div_eq_mul_inv, one_mul] using hh

theorem glyz_integer_grid_boundary_separation (F : ℕ) (u v : ℤ) (j l : ℕ) :
    glyzDyadicScale F / 3 ≤
      |((u : ℝ) + glyzDyadicScale F * j) -
        (1 / 3 + (v : ℝ) + glyzDyadicScale F * l)| := by
  have hc : glyzDyadicScale F * (2 : ℝ) ^ F = 1 := inv_mul_cancel₀ (by positivity)
  have he (w : ℤ) (i : ℕ) :
      glyzDyadicScale F * (w * (2 : ℤ) ^ F + i : ℤ) = (w : ℝ) + glyzDyadicScale F * i := by
    push_cast
    calc
      _ = (w : ℝ) * (glyzDyadicScale F * (2 : ℝ) ^ F) + glyzDyadicScale F * i := by ring
      _ = _ := by rw [hc, mul_one]
  have h := glyz_dyadic_boundary_separation F (u * (2 : ℤ) ^ F + j) (v * (2 : ℤ) ^ F + l)
  rw [he, he] at h
  simpa only [add_assoc] using h

theorem glyz_cell_margin_or_boundary (F : ℕ) (s : ℝ) {x : ℝ}
    (hx : x ∈ Icc s (s + 1)) :
    (∃ j : Fin (2 ^ F), Icc (x - glyzDyadicScale F / 12) (x + glyzDyadicScale F / 12) ⊆
      glyzShiftedOpenCell F s j) ∨
      ∃ j : ℕ, |x - (s + glyzDyadicScale F * j)| ≤ glyzDyadicScale F / 12 := by
  have hδ := glyzDyadicScale_pos F
  have hunit : x - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rcases glyz_unit_cell_or_boundary F hunit with ⟨j, hj⟩ | ⟨j, hj⟩
  · by_cases hl : s + glyzDyadicLeft F j < x - glyzDyadicScale F / 12
    · by_cases hr : x + glyzDyadicScale F / 12 < s + glyzDyadicRight F j
      · exact Or.inl ⟨j, fun t ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩⟩
      · right
        refine ⟨j + 1, ?_⟩
        have hright : x < s + glyzDyadicScale F * ((j : ℝ) + 1) := by
          change _ ∧ x - s < glyzDyadicScale F * ((j : ℝ) + 1) at hj
          linarith [hj.2]
        push_cast
        rw [abs_of_nonpos (by linarith : x - (s + glyzDyadicScale F * ((j : ℝ) + 1)) ≤ 0)]
        change ¬ x + glyzDyadicScale F / 12 < s + glyzDyadicScale F * ((j : ℝ) + 1) at hr
        linarith
    · right
      refine ⟨j, ?_⟩
      have hleft : s + glyzDyadicScale F * j < x := by
        change glyzDyadicScale F * j < x - s ∧ _ at hj
        linarith [hj.1]
      rw [abs_of_nonneg (by linarith : 0 ≤ x - (s + glyzDyadicScale F * j))]
      change ¬ s + glyzDyadicScale F * j < x - glyzDyadicScale F / 12 at hl
      linarith
  · exact Or.inr ⟨j, by rw [show x = s + glyzDyadicScale F * j by linarith, sub_self, abs_zero]; positivity⟩

def glyzOrdinaryGridIndex (s : Fin 2) : Fin 5 := ⟨s, by omega⟩
def glyzAlternateGridIndex (s : Fin 3) : Fin 5 := ⟨s + 2, by omega⟩

theorem glyzSmoothGridShift_ordinary (s : Fin 2) :
    glyzSmoothGridShift (glyzOrdinaryGridIndex s) = (s : ℝ) - 1 := by
  fin_cases s <;> norm_num [glyzSmoothGridShift, glyzOrdinaryGridIndex]

theorem glyzSmoothGridShift_alternate (s : Fin 3) :
    glyzSmoothGridShift (glyzAlternateGridIndex s) = 1 / 3 + ((s : ℝ) - 2) := by
  fin_cases s <;> norm_num [glyzSmoothGridShift, glyzAlternateGridIndex]

theorem glyz_five_grids_uniform_margin (F : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    ∃ s : Fin 5, ∃ j : Fin (2 ^ F),
      Icc (x - glyzDyadicScale F / 12) (x + glyzDyadicScale F / 12) ⊆
        glyzShiftedOpenCell F (glyzSmoothGridShift s) j := by
  obtain ⟨s, hs⟩ : ∃ s : Fin 2, x ∈ Icc (glyzSmoothGridShift (glyzOrdinaryGridIndex s))
      (glyzSmoothGridShift (glyzOrdinaryGridIndex s) + 1) := by
    by_cases h : x ≤ 0
    · exact ⟨0, by simpa [glyzSmoothGridShift, glyzOrdinaryGridIndex] using And.intro hx.1 h⟩
    · exact ⟨1, by simpa [glyzSmoothGridShift, glyzOrdinaryGridIndex] using And.intro (le_of_lt (lt_of_not_ge h)) hx.2⟩
  rcases glyz_cell_margin_or_boundary F _ hs with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨glyzOrdinaryGridIndex s, j, hj⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin 3, x ∈ Icc (glyzSmoothGridShift (glyzAlternateGridIndex t))
      (glyzSmoothGridShift (glyzAlternateGridIndex t) + 1) := by
    by_cases h : x ≤ -2 / 3
    · refine ⟨0, ?_⟩
      rw [glyzSmoothGridShift_alternate]
      norm_num
      constructor <;> linarith [hx.1]
    · by_cases h' : x ≤ 1 / 3
      · refine ⟨1, ?_⟩
        rw [glyzSmoothGridShift_alternate]
        norm_num
        constructor <;> linarith
      · refine ⟨2, ?_⟩
        rw [glyzSmoothGridShift_alternate]
        norm_num
        constructor <;> linarith [hx.2]
  rcases glyz_cell_margin_or_boundary F _ ht with ⟨l, hl⟩ | ⟨l, hl⟩
  · exact ⟨glyzAlternateGridIndex t, l, hl⟩
  have hsep := glyz_integer_grid_boundary_separation F ((s : ℤ) - 1) ((t : ℤ) - 2) j l
  push_cast at hsep
  rw [← glyzSmoothGridShift_ordinary s, ← glyzSmoothGridShift_alternate t] at hsep
  have htri := abs_sub_le (glyzSmoothGridShift (glyzOrdinaryGridIndex s) + glyzDyadicScale F * j)
    x (glyzSmoothGridShift (glyzAlternateGridIndex t) + glyzDyadicScale F * l)
  rw [abs_sub_comm (glyzSmoothGridShift (glyzOrdinaryGridIndex s) + glyzDyadicScale F * j) x] at htri
  exact False.elim (by linarith [glyzDyadicScale_pos F])

def glyzClampedTimeCenter (c : ℝ) : ℝ := max (-1) (min 1 c)

theorem glyzClampedTimeCenter_mem (c : ℝ) : glyzClampedTimeCenter c ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem glyzClampedTimeCenter_distance {h c : ℝ} (hh : 0 ≤ h)
    (hc : c ∈ Icc (-1 - h) (1 + h)) : |c - glyzClampedTimeCenter c| ≤ h := by
  by_cases hlow : c < -1
  · rw [glyzClampedTimeCenter, min_eq_right (by linarith), max_eq_left hlow.le,
      abs_of_nonpos (by linarith)]
    linarith [hc.1]
  · by_cases hhigh : 1 < c
    · rw [glyzClampedTimeCenter, min_eq_left hhigh.le, max_eq_right (by norm_num),
        abs_of_nonneg (by linarith)]
      linarith [hc.2]
    · rw [glyzClampedTimeCenter, min_eq_right (by linarith), max_eq_right (by linarith), sub_self, abs_zero]
      exact hh

/-- A whole standard smooth-cutoff support, after restriction to the
original time domain, fits in one coarse cell with a uniform margin. -/
theorem exists_glyz_standard_interval_cell (F : ℕ) {h c : ℝ} (hh : 0 < h)
    (hsmall : 24 * h ≤ glyzDyadicScale F)
    (hc : c ∈ Icc (-1 - h) (1 + h)) :
    ∃ s : Fin 5, ∃ j : Fin (2 ^ F),
      Icc (c - h) (c + h) ∩ Icc (-1 : ℝ) 1 ⊆
        glyzShiftedOpenCell F (glyzSmoothGridShift s) j ∧
      c ∈ Icc (glyzSmoothGridShift s + glyzDyadicLeft F j - h)
        (glyzSmoothGridShift s + glyzDyadicRight F j + h) := by
  let x := glyzClampedTimeCenter c
  have hx := glyzClampedTimeCenter_mem c
  have hd := glyzClampedTimeCenter_distance hh.le hc
  obtain ⟨s, j, hj⟩ := glyz_five_grids_uniform_margin F hx
  refine ⟨s, j, ?_, ?_⟩
  · intro t ht
    apply hj
    have hab := abs_le.mp hd
    constructor <;> try simp only [x] at *
    all_goals
      linarith [ht.1.1, ht.1.2, hab.1, hab.2]
  · have hm : x ∈ Icc (x - glyzDyadicScale F / 12) (x + glyzDyadicScale F / 12) := by
      constructor <;> linarith [glyzDyadicScale_pos F]
    have hxcell := hj hm
    have hab := abs_le.mp hd
    change glyzSmoothGridShift s + glyzDyadicLeft F j < x ∧
      x < glyzSmoothGridShift s + glyzDyadicRight F j at hxcell
    constructor <;> try simp only [x] at *
    all_goals
      linarith [hxcell.1, hxcell.2, hab.1, hab.2]

/-- Residue colors distinguish every pair of exact fine intervals
assigned to the same coarse cell. The number 4096 is fixed. -/
theorem exists_glyz_standard_grid_assignment (F M : ℕ) {h : ℝ} (hh : 0 < h)
    (hsmall : 24 * h ≤ glyzDyadicScale F) (hlarge : glyzDyadicScale F ≤ 2048 * h)
    (hcenters : ∀ j : Fin M, (-1 : ℝ) + h * j ∈ Icc (-1 - h) (1 + h)) :
    ∃ (s : Fin M → Fin 5) (l : Fin M → Fin (2 ^ F)),
      (∀ j : Fin M, Icc (-1 + h * j - h) (-1 + h * j + h) ∩ Icc (-1 : ℝ) 1 ⊆
        glyzShiftedOpenCell F (glyzSmoothGridShift (s j)) (l j)) ∧
      Function.Injective (fun j : Fin M =>
        ((s j, (⟨(j : ℕ) % 4096, Nat.mod_lt _ (by norm_num)⟩ : Fin 4096)), l j)) := by
  classical
  have hloc (j : Fin M) := exists_glyz_standard_interval_cell F hh hsmall (hcenters j)
  choose s l hs hc using hloc
  refine ⟨s, l, hs, ?_⟩
  intro j j' he
  have hs' : s j = s j' := congrArg (fun q => q.1.1) he
  have hl' : l j = l j' := congrArg Prod.snd he
  have hm : (j : ℕ) % 4096 = (j' : ℕ) % 4096 := congrArg (fun q => (q.1.2 : Fin 4096).val) he
  have h1 := hc j
  have h2 := hc j'
  rw [← hs', ← hl'] at h2
  have hlength := glyzShiftedOpenCell_length F (l j) (glyzSmoothGridShift (s j))
  have hjR : (j : ℝ) < (j' : ℝ) + 4096 := by
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hjR' : (j' : ℝ) < (j : ℝ) + 4096 := by
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hjN : (j : ℕ) < (j' : ℕ) + 4096 := by exact_mod_cast hjR
  have hjN' : (j' : ℕ) < (j : ℕ) + 4096 := by exact_mod_cast hjR'
  apply Fin.ext
  omega

end PlanarNikodym
