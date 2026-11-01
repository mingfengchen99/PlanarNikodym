import PlanarNikodym.Analysis.Fourier.GlyzCurveScaleIteration
import PlanarNikodym.Analysis.Fourier.GlyzCurveDepthSchedule

/-! Exact loss accounting for the finite Taylor iteration. The exponent
increments telescope, so a fixed number of iterations has a uniform
coefficient independent of the finest depth. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyz_curve_step_product (M : ℕ) (n : ℕ → ℕ) (C α : ℝ)
    (hmono : ∀ j < M, n j ≤ n (j + 1)) :
    (∏ j ∈ Finset.range M, C * (2 : ℝ) ^ (α * (n (j + 1) - n j : ℕ))) =
      C ^ M * (2 : ℝ) ^ (α * ((n M : ℝ) - n 0)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2), ← Finset.mul_sum]
  have hsum : (∑ j ∈ Finset.range M, ((n (j + 1) - n j : ℕ) : ℝ)) =
      (n M : ℝ) - n 0 := by
    calc
      _ = ∑ j ∈ Finset.range M, ((n (j + 1) : ℝ) - n j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Nat.cast_sub (hmono j (Finset.mem_range.mp hj))
      _ = _ := Finset.sum_range_sub (fun j => (n j : ℝ)) M
  rw [hsum]

/-- The finite-step coefficient is bounded by the requested epsilon
loss. The factor outside that loss depends only on the finite schedule. -/
theorem glyz_curve_iteration_coefficient_le
    (N M : ℕ) (n : ℕ → ℕ) {C ε B : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hmono : ∀ j < M, n j ≤ n (j + 1))
    (hfinest : n M = N) (hinit : (n 0 : ℝ) ≤ ε / 2 * N + B) :
    ((2 : ℝ) ^ n 0 *
      ∏ j ∈ Finset.range M, C * (2 : ℝ) ^ (ε / 2 * (n (j + 1) - n j : ℕ))) ≤
        (C ^ M * (2 : ℝ) ^ B) * (2 : ℝ) ^ (ε * N) := by
  rw [glyz_curve_step_product M n C (ε / 2) hmono, hfinest]
  have he : (n 0 : ℝ) + ε / 2 * ((N : ℝ) - n 0) ≤ B + ε * N := by
    have hn : 0 ≤ ε / 2 * (n 0 : ℝ) := mul_nonneg (by positivity) (Nat.cast_nonneg _)
    linarith
  calc
    _ = C ^ M * (2 : ℝ) ^ ((n 0 : ℝ) + ε / 2 * ((N : ℝ) - n 0)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
      ring
    _ ≤ C ^ M * (2 : ℝ) ^ (B + ε * N) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (pow_nonneg hC _)
    _ = _ := by rw [Real.rpow_add (by norm_num)]; ring

/-- Once genuine moment estimates have supplied every refinement, the
finite Taylor schedule yields the full uniform epsilon estimate. -/
theorem glyz_curve_scheduled_iteration
    (l N M K : ℕ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ)
    (p : ℝ≥0) (hp : 1 ≤ p) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hM : ((l : ℝ) / (l + 1)) ^ M ≤ ε / 2)
    (hstep : ∀ j < M, ∀ i < 2 ^ glyzCurveDepth l M K N j,
      lpNorm ((glyzDyadicBlock f N (glyzCurveDepth l M K N j) i :
        SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2 ≤
        (C * (2 : ℝ) ^ (ε / 2 *
          (glyzCurveDepth l M K N (j + 1) - glyzCurveDepth l M K N j : ℕ))) *
        glyzDyadicBlock
          (fun k => lpNorm ((glyzDyadicBlock f N (glyzCurveDepth l M K N (j + 1)) k :
            SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2)
          (glyzCurveDepth l M K N (j + 1)) (glyzCurveDepth l M K N j) i) :
    lpNorm ((∑ i ∈ Finset.range (2 ^ N), f i : SchwartzMap (GlyzSpace l) ℂ) :
      GlyzSpace l → ℂ) p volume ^ 2 ≤
      (C ^ M * (2 : ℝ) ^ ((K : ℝ) + (l : ℝ) ^ M)) *
        (2 : ℝ) ^ (ε * N) *
        ∑ i ∈ Finset.range (2 ^ N), lpNorm (f i : GlyzSpace l → ℂ) p volume ^ 2 := by
  let n := glyzCurveDepth l M K N
  have hm : ∀ j < M, n j ≤ n (j + 1) := glyzCurveDepth_mono l M K N
  have hfin : n M = N := glyzCurveDepth_finest l M K N
  have hi : (n 0 : ℝ) ≤ ε / 2 * N + ((K : ℝ) + (l : ℝ) ^ M) := by
    apply (glyzCurveDepth_initial_le l M K N).trans
    gcongr
  have h := glyz_curve_finite_iteration l N M f n (glyzCurveDepth_le l M K N 0) hfin p hp
    (fun j => C * (2 : ℝ) ^ (ε / 2 * (n (j + 1) - n j : ℕ))) hm
    (fun _ _ => mul_nonneg hC (by positivity)) hstep
  exact h.trans (mul_le_mul_of_nonneg_right
    (glyz_curve_iteration_coefficient_le N M n hC hε hm hfin hi)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end PlanarNikodym
