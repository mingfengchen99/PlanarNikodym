import PlanarNikodym.Analysis.Fourier.GlyzDyadicNestedBlocks

/-! Actual dyadic interval endpoints and separation inherited from
one nonzero descendant. These facts allow zero pieces outside a
separated interval in the projected-curve argument. -/
noncomputable section
open Set
namespace PlanarNikodym

def glyzDyadicLeft (n i : ℕ) : ℝ := glyzDyadicScale n * i
def glyzDyadicRight (n i : ℕ) : ℝ := glyzDyadicScale n * ((i : ℝ) + 1)

theorem glyzDyadicInterval_length (n i : ℕ) :
    glyzDyadicRight n i - glyzDyadicLeft n i = glyzDyadicScale n := by
  unfold glyzDyadicLeft glyzDyadicRight
  ring

theorem glyzDyadicLeft_lt_right (n i : ℕ) :
    glyzDyadicLeft n i < glyzDyadicRight n i := by
  have h := glyzDyadicScale_pos n
  have he := glyzDyadicInterval_length n i
  linarith

theorem glyzDyadicInterval_subset_unit {n i : ℕ} (hi : i < 2 ^ n) :
    Icc (glyzDyadicLeft n i) (glyzDyadicRight n i) ⊆ Icc (0 : ℝ) 1 := by
  have hl : 0 ≤ glyzDyadicLeft n i := mul_nonneg (glyzDyadicScale_pos n).le (Nat.cast_nonneg i)
  have hi' : (i : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hi
  have hr : glyzDyadicRight n i ≤ 1 := by
    calc
      _ ≤ glyzDyadicScale n * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hi' (glyzDyadicScale_pos n).le
      _ = 1 := inv_mul_cancel₀ (by positivity)
  exact fun x hx => ⟨hl.trans hx.1, hx.2.trans hr⟩

theorem glyzDyadicCenter_descendant_mem_interval {n q i j : ℕ} (hj : j < 2 ^ q) :
    glyzDyadicCenter (n + q) (i * 2 ^ q + j) ∈
      Icc (glyzDyadicLeft n i) (glyzDyadicRight n i) := by
  rw [← glyzDyadicCenter_rescale]
  have h := glyzDyadicCenter_mem_Icc hj
  have hn := glyzDyadicScale_pos n
  change glyzDyadicScale n * i ≤ _ ∧ _ ≤ glyzDyadicScale n * ((i : ℝ) + 1)
  constructor <;> nlinarith [h.1, h.2]

theorem glyz_dyadic_interval_separated_of_descendant {n q i j : ℕ} {ν t : ℝ}
    (hi : i < 2 ^ n) (hj : j < 2 ^ q) (hscale : glyzDyadicScale n ≤ ν / 2)
    (hsep : (glyzDyadicCenter (n + q) (i * 2 ^ q + j), t) ∈ separatedMixedCenters ν) :
    ∀ x ∈ Icc (glyzDyadicLeft n i) (glyzDyadicRight n i),
      (x, t) ∈ separatedMixedCenters (ν / 2) := by
  intro x hx
  have hw := glyzDyadicCenter_descendant_mem_interval (n := n) (i := i) hj
  have hx01 := glyzDyadicInterval_subset_unit hi hx
  refine ⟨⟨by linarith [hx01.1], hx01.2⟩, hsep.2.1, ?_⟩
  have hd : |glyzDyadicCenter (n + q) (i * 2 ^ q + j) - x| ≤ glyzDyadicScale n := by
    rw [← glyzDyadicInterval_length n i]
    exact abs_le.mpr ⟨by linarith [hw.1, hw.2, hx.1, hx.2],
      by linarith [hw.1, hw.2, hx.1, hx.2]⟩
  have ht := abs_sub_le (glyzDyadicCenter (n + q) (i * 2 ^ q + j)) x t
  linarith [hsep.2.2]

theorem glyzDyadicBlock_nonzero_descendant {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N n i : ℕ) (hf : glyzDyadicBlock f N n i ≠ 0) :
    ∃ j < 2 ^ (N - n), f (i * 2 ^ (N - n) + j) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hf
  exact Finset.sum_eq_zero fun j hj => h j (Finset.mem_range.mp hj)

/-- Separation of nonzero finest pieces gives separation throughout
every short nonzero parent interval. -/
theorem glyz_dyadic_interval_separated_of_block {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N n i : ℕ) {ν t : ℝ} (hn : n ≤ N) (hi : i < 2 ^ n)
    (hscale : glyzDyadicScale n ≤ ν / 2)
    (hs : ∀ k < 2 ^ N, f k ≠ 0 → (glyzDyadicCenter N k, t) ∈ separatedMixedCenters ν)
    (hf : glyzDyadicBlock f N n i ≠ 0) :
    ∀ x ∈ Icc (glyzDyadicLeft n i) (glyzDyadicRight n i),
      (x, t) ∈ separatedMixedCenters (ν / 2) := by
  obtain ⟨j, hj, hjf⟩ := glyzDyadicBlock_nonzero_descendant f N n i hf
  have he : n + (N - n) = N := Nat.add_sub_of_le hn
  have hk : i * 2 ^ (N - n) + j < 2 ^ N := by
    simpa only [he] using glyz_dyadic_descendant_lt hi hj
  apply glyz_dyadic_interval_separated_of_descendant hi hj hscale
  simpa only [he] using hs _ hk hjf

end PlanarNikodym
