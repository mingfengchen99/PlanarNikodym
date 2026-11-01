import PlanarNikodym.Analysis.Fourier.GlyzCurveMomentStep
import PlanarNikodym.Analysis.Fourier.GlyzCurveIterationLoss
import PlanarNikodym.Analysis.Fourier.GlyzDyadicIntervalGeometry

/-! Uniform full-scale decoupling of the actual projected polynomial
curves used in GLYZ. The analytic induction premise concerns only the
ordinary lower-dimensional moment curve. A fixed finite Taylor iteration
proves the controlled-curve conclusion, including arbitrary fixed box
enlargement and zero pieces outside separated parameter intervals. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators NNReal ENNReal
namespace PlanarNikodym

private theorem glyzDyadicScale_antitone' {n m : ℕ} (hnm : n ≤ m) :
    glyzDyadicScale m ≤ glyzDyadicScale n := by
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnm)

/-- The genuine GL4 dyadic controlled-curve estimate. The sole analytic
premise is zero optimal loss for the ordinary moment curve in dimension
`l`; there is no assumed estimate for projected curves, enlarged boxes,
or grouped pieces. The coefficient is chosen before `N`, `t`, and `f`. -/
theorem glyz_controlled_curve_decoupling_of_moment_optimal_zero
    (l r : ℕ) {p : ℝ≥0} (hp : 1 ≤ p)
    (hη : glyzOptimalSquareLoss l p = 0)
    {ν Q ε : ℝ} (hν : 0 < ν) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (t : ℝ)
      (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      (∀ j < 2 ^ N, f j ≠ 0 →
        (glyzDyadicCenter N j, t) ∈ separatedMixedCenters ν) →
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox (glyzCoordinateCurve l r t) l
          (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((∑ j ∈ Finset.range (2 ^ N), f j : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) p volume ^ 2 ≤
        A * (2 : ℝ) ^ (ε * N) *
          ∑ j ∈ Finset.range (2 ^ N), lpNorm (f j : GlyzSpace l → ℂ) p volume ^ 2 := by
  have hα : GlyzAdmissibleSquareLoss l p (ε / 2) :=
    glyz_admissible_square_loss_of_optimal_lt l p hp (by rw [hη]; positivity)
  obtain ⟨ρ, C, hρ, hρ1, hC, hstep⟩ :=
    exists_uniform_glyz_curve_step_of_admissible_square_loss l r
      (show 0 < ν / 2 by positivity) hQ hp hα
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one
    (lt_min hρ (show 0 < ν / 2 by positivity)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hKscale : glyzDyadicScale K < min ρ (ν / 2) := by
    simpa only [glyzDyadicScale, one_div, inv_pow] using hK
  have hratio : (l : ℝ) / (l + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity) hratio
  refine ⟨C ^ M * (2 : ℝ) ^ ((K : ℝ) + (l : ℝ) ^ M),
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hC) _) (by positivity), fun N t f hs hf => ?_⟩
  apply glyz_curve_scheduled_iteration l N M K f p hp
    (le_trans zero_le_one hC) hε.le hM.le
  intro j hj i hi
  let n := glyzCurveDepth l M K N j
  let m := glyzCurveDepth l M K N (j + 1)
  have hnm : n ≤ m := glyzCurveDepth_mono l M K N j hj
  have hmN : m ≤ N := glyzCurveDepth_le l M K N (j + 1)
  have hnN : n ≤ N := glyzCurveDepth_le l M K N j
  change lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) :
      GlyzSpace l → ℂ) p volume ^ 2 ≤
    (C * (2 : ℝ) ^ (ε / 2 * (m - n : ℕ))) *
      glyzDyadicBlock (fun k => lpNorm ((glyzDyadicBlock f N m k :
        SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2) m n i
  by_cases heq : n = m
  · rw [← heq]
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one,
      glyzDyadicBlock_finest]
    exact le_mul_of_one_le_left (sq_nonneg _) hC
  · have hKN : K ≤ N := by
      by_contra hk
      have hn : n = N := min_eq_left (le_trans (by omega) (le_max_left _ _))
      have hm : m = N := min_eq_left (le_trans (by omega) (le_max_left _ _))
      exact heq (hn.trans hm.symm)
    have hKn : K ≤ n := glyzCurveDepth_ge l M K N j hKN
    have hshort : glyzDyadicScale n < ρ :=
      (glyzDyadicScale_antitone' hKn).trans_lt (hKscale.trans_le (min_le_left _ _))
    have hsmall : glyzDyadicScale n ≤ ν / 2 :=
      (glyzDyadicScale_antitone' hKn).trans (hKscale.le.trans (min_le_right _ _))
    by_cases hz : glyzDyadicBlock f N n i = 0
    · rw [hz]
      simp only [FunLike.coe_zero, lpNorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      apply mul_nonneg (mul_nonneg (le_trans zero_le_one hC) (by positivity))
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    · have hsep := glyz_dyadic_interval_separated_of_block f N n i hnN hi hsmall hs hz
      apply hstep t N n m i hnm hmN hi hshort (glyzDyadicScale_antitone' hnm)
        (glyzCurveDepth_taylor_condition l M K N j hj)
      · exact hsep _ ⟨le_rfl, (glyzDyadicLeft_lt_right n i).le⟩
      · intro k hk
        have he : n + (m - n) = m := Nat.add_sub_of_le hnm
        apply hsep
        simpa only [he] using glyzDyadicCenter_descendant_mem_interval (n := n) (i := i) hk
      · exact hf

end PlanarNikodym
