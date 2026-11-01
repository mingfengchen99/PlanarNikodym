import PlanarNikodym.Analysis.Fourier.GlyzGeneralCurveStep
import PlanarNikodym.Analysis.Fourier.GlyzCurveIterationLoss
import PlanarNikodym.Analysis.Fourier.GlyzCriticalMomentDecoupling

/-! Uniform critical decoupling for arbitrary C^(l+1) nondegenerate
curves, under actual derivative and jet-determinant bounds. The moment
estimate is proved; the final critical theorem has no analytic premise. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyz_general_curve_decoupling_of_moment_optimal_zero
    (l : ℕ) {p : ℝ≥0} (hp : 1 ≤ p) (hη : glyzOptimalSquareLoss l p = 0)
    {β B Q ε : ℝ} (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((∑ j ∈ Finset.range (2 ^ N), f j : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) p volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) *
          ∑ j ∈ Finset.range (2 ^ N), lpNorm (f j : GlyzSpace l → ℂ) p volume ^ 2 := by
  have hα : GlyzAdmissibleSquareLoss l p (ε / 2) :=
    glyz_admissible_square_loss_of_optimal_lt l p hp (by rw [hη]; positivity)
  obtain ⟨ρ, C, hρ, _hρ1, hC, hstep⟩ := exists_uniform_glyz_general_curve_step l hβ hB hQ hp hα
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hρ (by norm_num : (1 / 2 : ℝ) < 1)
  have hKscale : glyzDyadicScale K < ρ := by
    simpa only [glyzDyadicScale, one_div, inv_pow] using hK
  have hratio : (l : ℝ) / (l + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity) hratio
  refine ⟨C ^ M * (2 : ℝ) ^ ((K : ℝ) + (l : ℝ) ^ M),
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hC) _) (by positivity),
    fun γ hγ hder hdet N f hf => ?_⟩
  apply glyz_curve_scheduled_iteration l N M K f p hp (le_trans zero_le_one hC) hε.le hM.le
  intro j hj i hi
  let n := glyzCurveDepth l M K N j
  let m := glyzCurveDepth l M K N (j + 1)
  have hnm : n ≤ m := glyzCurveDepth_mono l M K N j hj
  have hmN : m ≤ N := glyzCurveDepth_le l M K N (j + 1)
  change lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzSpace l) ℂ) :
      GlyzSpace l → ℂ) p volume ^ 2 ≤
    (C * (2 : ℝ) ^ (ε / 2 * (m - n : ℕ))) *
      glyzDyadicBlock (fun k => lpNorm ((glyzDyadicBlock f N m k :
        SchwartzMap (GlyzSpace l) ℂ) : GlyzSpace l → ℂ) p volume ^ 2) m n i
  by_cases heq : n = m
  · rw [← heq]
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one, glyzDyadicBlock_finest]
    exact le_mul_of_one_le_left (sq_nonneg _) hC
  · have hKN : K ≤ N := by
      by_contra hk
      have hn : n = N := min_eq_left (le_trans (by omega) (le_max_left _ _))
      have hm : m = N := min_eq_left (le_trans (by omega) (le_max_left _ _))
      exact heq (hn.trans hm.symm)
    have hKn : K ≤ n := glyzCurveDepth_ge l M K N j hKN
    exact hstep γ hγ hder hdet N n m i hnm hmN hi
      ((glyzDyadicScale_antitone hKn).trans_lt hKscale)
      (glyzCurveDepth_taylor_condition l M K N j hj) f hf

/-- Theorem 3.6 for the actual Schwartz dyadic curve boxes, uniformly
over the entire finite-regularity curve class. -/
theorem glyz_general_curve_critical_decoupling
    (l : ℕ) (hl : 0 < l) {β B Q ε : ℝ}
    (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ → GlyzSpace l,
      ContDiff ℝ (l + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ l + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzSpace l) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzSpace l → ℂ)) ⊆
        glyzEnlargedCurveBox γ l (glyzDyadicCenter N j) (glyzDyadicScale N) Q) →
      lpNorm ((∑ j ∈ Finset.range (2 ^ N), f j : SchwartzMap (GlyzSpace l) ℂ) :
        GlyzSpace l → ℂ) (glyzCriticalNNExponent l) volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) * ∑ j ∈ Finset.range (2 ^ N),
          lpNorm (f j : GlyzSpace l → ℂ) (glyzCriticalNNExponent l) volume ^ 2 :=
  glyz_general_curve_decoupling_of_moment_optimal_zero l
    (one_le_glyzCriticalNNExponent hl) (glyz_critical_optimal_square_loss_eq_zero l hl)
    hβ hB hQ hε

end PlanarNikodym
