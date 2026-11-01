import PlanarNikodym.Analysis.Fourier.GlyzDyadicRescaling

/-! A finite dyadic depth schedule for the Taylor approximation condition.
Integer rounding is performed only once. The number of refinement steps
depends on the requested loss, and never on the finest dyadic depth. -/
noncomputable section
namespace PlanarNikodym

def glyzCurveRawDepth (l M N j : ℕ) : ℕ :=
  l ^ (M - j) * (l + 1) ^ j * (N / (l + 1) ^ M + 1)

/-- Clamp a geometrically spaced sequence between a prescribed
short-interval threshold and the finest depth. -/
def glyzCurveDepth (l M K N j : ℕ) : ℕ :=
  min N (max K (glyzCurveRawDepth l M N j))

theorem glyzCurveRawDepth_ratio (l M N j : ℕ) (hj : j < M) :
    (l + 1) * glyzCurveRawDepth l M N j =
      l * glyzCurveRawDepth l M N (j + 1) := by
  have he : M - j = M - (j + 1) + 1 := by omega
  simp only [glyzCurveRawDepth, he, pow_succ]
  ring

theorem glyzCurveRawDepth_mono (l M N j : ℕ) (hj : j < M) :
    glyzCurveRawDepth l M N j ≤ glyzCurveRawDepth l M N (j + 1) := by
  have h := glyzCurveRawDepth_ratio l M N j hj
  nlinarith

theorem glyzCurveDepth_le (l M K N j : ℕ) : glyzCurveDepth l M K N j ≤ N :=
  min_le_left _ _

theorem glyzCurveDepth_ge (l M K N j : ℕ) (hKN : K ≤ N) :
    K ≤ glyzCurveDepth l M K N j :=
  le_min hKN (le_max_left _ _)

theorem glyzCurveDepth_mono (l M K N j : ℕ) (hj : j < M) :
    glyzCurveDepth l M K N j ≤ glyzCurveDepth l M K N (j + 1) :=
  min_le_min le_rfl (max_le_max le_rfl (glyzCurveRawDepth_mono l M N j hj))

theorem glyzCurveDepth_finest (l M K N : ℕ) : glyzCurveDepth l M K N M = N := by
  have hN : N < (l + 1) ^ M * (N / (l + 1) ^ M + 1) :=
    Nat.lt_mul_div_succ N (by positivity)
  apply min_eq_left
  apply le_trans (Nat.le_of_lt hN)
  simpa only [glyzCurveRawDepth, Nat.sub_self, pow_zero, one_mul] using
    le_max_right K (glyzCurveRawDepth l M N M)

/-- Clamping preserves exactly the inequality needed by Taylor
approximation, including intervals shorter than the cutoff depth. -/
theorem glyzCurveDepth_ratio (l M K N j : ℕ) (hj : j < M) :
    l * glyzCurveDepth l M K N (j + 1) ≤
      (l + 1) * glyzCurveDepth l M K N j := by
  unfold glyzCurveDepth
  rw [mul_min, mul_min, mul_max, mul_max]
  apply min_le_min
  · exact Nat.mul_le_mul_right N (by omega)
  · exact max_le_max (Nat.mul_le_mul_right K (by omega))
      (le_of_eq (glyzCurveRawDepth_ratio l M N j hj).symm)

theorem glyzCurveDepth_initial_le (l M K N : ℕ) :
    (glyzCurveDepth l M K N 0 : ℝ) ≤
      ((l : ℝ) / (l + 1)) ^ M * N + ((K : ℝ) + (l : ℝ) ^ M) := by
  have hB : (0 : ℝ) < ((l : ℝ) + 1) ^ M := by positivity
  have hdiv : ((N / (l + 1) ^ M : ℕ) : ℝ) * ((l : ℝ) + 1) ^ M ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N ((l + 1) ^ M)
  have hmul : (l : ℝ) ^ M * (N / (l + 1) ^ M : ℕ) ≤
      (l : ℝ) ^ M / ((l : ℝ) + 1) ^ M * N := by
    calc
      _ ≤ (l : ℝ) ^ M * ((N : ℝ) / ((l : ℝ) + 1) ^ M) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ hB).mpr hdiv) (by positivity)
      _ = _ := by ring
  have hclamp : glyzCurveDepth l M K N 0 ≤ K + glyzCurveRawDepth l M N 0 := by
    exact (min_le_right _ _).trans (max_le (by omega) (by omega))
  have hcast := (Nat.cast_le (α := ℝ)).mpr hclamp
  simp only [glyzCurveRawDepth, Nat.sub_zero, pow_zero, mul_one,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] at hcast
  rw [div_pow]
  nlinarith

/-- The exact dyadic form of the analytic Taylor scale restriction. -/
theorem glyzDyadicScale_taylor_condition (l n m : ℕ) (h : l * m ≤ (l + 1) * n) :
    glyzDyadicScale n ^ (l + 1) ≤ glyzDyadicScale m ^ l := by
  unfold glyzDyadicScale
  rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul]
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  simpa only [Nat.mul_comm] using h

theorem glyzCurveDepth_taylor_condition (l M K N j : ℕ) (hj : j < M) :
    glyzDyadicScale (glyzCurveDepth l M K N j) ^ (l + 1) ≤
      glyzDyadicScale (glyzCurveDepth l M K N (j + 1)) ^ l :=
  glyzDyadicScale_taylor_condition _ _ _ (glyzCurveDepth_ratio l M K N j hj)

end PlanarNikodym
