import PlanarNikodym.Analysis.Fourier.GlyzConeDyadicStep
import PlanarNikodym.Analysis.Fourier.GlyzFixedStepSchedule

/-! Critical decoupling for each fixed radial slab of a general
nondegenerate cone. The angular iteration is performed on the actual
Schwartz blocks, with a fixed increment chosen after the uniform
moment coefficient, before the curve and finest depth. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform NNReal ENNReal BigOperators
namespace PlanarNikodym

/-- A genuine epsilon estimate on a sufficiently narrow but fixed radial
slab. The slab width and coefficient are uniform over the full controlled
curve class and every nonzero radial center. -/
theorem glyz_truncated_cone_critical_decoupling
    (k : ℕ) (hk : 0 < k) {β B Q ε : ℝ}
    (hβ : 0 < β) (hB : 0 < B) (hQ : 0 < Q) (hε : 0 < ε) :
    ∃ σ C : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < C ∧ ∀ γ : ℝ → GlyzSpace k,
      ContDiff ℝ (k + 1 : ℕ) γ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ k + 1, ‖iteratedDeriv j γ s‖ ≤ B) →
      (∀ s ∈ Icc (0 : ℝ) 1, β ≤ |(glyzCurveJetOperator γ s).det|) →
      ∀ (a : ℝ), a ≠ 0 → ∀ (N : ℕ) (f : ℕ → SchwartzMap (GlyzConeSpace k) ℂ),
      (∀ j < 2 ^ N, Function.support (𝓕 (f j : GlyzConeSpace k → ℂ)) ⊆
        glyzTruncatedConeBox k γ (glyzDyadicCenter N j) (glyzDyadicScale N) Q a σ) →
      lpNorm ((∑ j ∈ Finset.range (2 ^ N), f j : SchwartzMap (GlyzConeSpace k) ℂ) :
        GlyzConeSpace k → ℂ) (glyzCriticalNNExponent k) volume ^ 2 ≤
        C * (2 : ℝ) ^ (ε * N) * ∑ j ∈ Finset.range (2 ^ N),
          lpNorm (f j : GlyzConeSpace k → ℂ) (glyzCriticalNNExponent k) volume ^ 2 := by
  have hp : (2 : ℝ≥0) ≤ glyzCriticalNNExponent k := by
    exact two_le_glyzCriticalNNExponent hk
  obtain ⟨ρ, C, hρ, _hρ1, hC, hsteps⟩ := exists_uniform_glyz_cone_dyadic_step k hβ hB hQ hp
    (glyz_critical_admissible_square_loss k hk (show 0 < ε / 2 by positivity))
  obtain ⟨q, hq, habsorb⟩ := exists_glyz_fixed_step_absorbing C hε
  obtain ⟨σ, hσ, hσ1, hstep⟩ := hsteps q
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hρ (by norm_num : (1 / 2 : ℝ) < 1)
  have hKscale : glyzDyadicScale K < ρ := by
    simpa only [glyzDyadicScale, one_div, inv_pow] using hK
  let n₀ := max K (k * q)
  refine ⟨σ, (2 : ℝ) ^ ((n₀ : ℝ) + ε * q), hσ, hσ1, by positivity,
    fun γ hγ hder hdet a ha N f hf => ?_⟩
  apply glyz_fixed_step_iteration n₀ q N hq f (glyzCriticalNNExponent k)
    (one_le_glyzCriticalNNExponent hk) (le_trans zero_le_one hC) hε.le habsorb
  intro j _hj i hi
  let n := glyzFixedDepth n₀ q N j
  let m := glyzFixedDepth n₀ q N (j + 1)
  have hnm : n ≤ m := glyzFixedDepth_mono n₀ q N j
  have hmN : m ≤ N := glyzFixedDepth_le n₀ q N (j + 1)
  have hdq : m - n ≤ q := by have h := glyzFixedDepth_increment n₀ q N j; omega
  change lpNorm ((glyzDyadicBlock f N n i : SchwartzMap (GlyzConeSpace k) ℂ) :
      GlyzConeSpace k → ℂ) (glyzCriticalNNExponent k) volume ^ 2 ≤
    (C * (2 : ℝ) ^ (ε / 2 * q)) * glyzDyadicBlock
      (fun u => lpNorm ((glyzDyadicBlock f N m u : SchwartzMap (GlyzConeSpace k) ℂ) :
        GlyzConeSpace k → ℂ) (glyzCriticalNNExponent k) volume ^ 2) m n i
  by_cases heq : n = m
  · rw [← heq, glyzDyadicBlock_finest]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_mul_of_one_le_of_one_le hC
      (Real.one_le_rpow (by norm_num) (by positivity)))
  · have hn₀N : n₀ ≤ N := by
      by_contra hn₀
      have hn : n = N := min_eq_left (by omega)
      have hm : m = N := min_eq_left (by omega)
      exact heq (hn.trans hm.symm)
    have hKn : K ≤ n := (le_max_left _ _).trans (glyzFixedDepth_ge n₀ q N j hn₀N)
    have hs := hstep γ hγ hder hdet N n m i hnm hmN hdq hi
      ((glyzDyadicScale_antitone hKn).trans_lt hKscale)
      (glyzFixedDepth_taylor_condition k n₀ q N j (le_max_right _ _)) a ha f hf
    apply hs.trans
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hC)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdq) (by positivity)
    · unfold glyzDyadicBlock
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end PlanarNikodym
