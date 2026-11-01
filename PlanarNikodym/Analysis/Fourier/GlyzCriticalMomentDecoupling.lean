import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricLowerDegreeGain
import PlanarNikodym.Analysis.Fourier.GlyzCriticalBootstrapClosure
import PlanarNikodym.Analysis.Fourier.GlyzDyadicL2

/-! Critical moment-curve decoupling in every positive dimension.
Strong induction supplies precisely the lower-dimensional zero-loss premise
of the actual slice gain. The degree-one case is the proved Fourier-overlap
L² estimate; the induction step uses finite real signed lower limits. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace PlanarNikodym

/-- The actual critical moment-curve squared decoupling exponent vanishes
in every positive dimension, with no analytic premise left in the statement. -/
theorem glyz_critical_optimal_square_loss_eq_zero (k : ℕ) (hk : 0 < k) :
    glyzOptimalSquareLoss k (glyzCriticalNNExponent k) = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk1 : k = 1
    · subst k
      have hp : glyzCriticalNNExponent 1 = 2 := by
        rw [show glyzCriticalNNExponent 1 =
          NNReal.mk (glyzCriticalExponent 1) (glyzCriticalExponent_nonneg 1) from rfl]
        ext
        norm_num [glyzCriticalExponent]
      rw [hp]
      exact glyzOptimalSquareLoss_l2_eq_zero 0
    · let A : ℕ := k * (k + 1) + 1
      have hA : k < A := by dsimp [A]; nlinarith
      have hQ : k * (k + 1) / 2 ≤ A := by
        exact (Nat.div_le_self _ _).trans (Nat.le_succ _)
      apply glyz_critical_optimal_zero_of_gain (by omega) hA
      intro j hj hjk alpha beta ha hab hb hb1 hab1
      exact glyz_critical_optimal_gain hj hjk hA hQ (ih j hjk hj)
        ha hab hb hb1 hab1

/-- Every positive epsilon is an admissible loss for the actual squared
critical decoupling constants, uniformly over all dyadic depths. -/
theorem glyz_critical_admissible_square_loss (k : ℕ) (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) :
    GlyzAdmissibleSquareLoss k (glyzCriticalNNExponent k) ε :=
  (glyzOptimalSquareLoss_eq_zero_iff k (glyzCriticalNNExponent k)
    (one_le_glyzCriticalNNExponent hk)).mp
      (glyz_critical_optimal_square_loss_eq_zero k hk) ε hε

/-- The explicit supported-Schwartz-family form of critical moment-curve
decoupling. The constant is chosen before the depth and the entire family. -/
theorem glyz_critical_moment_decoupling (k : ℕ) (hk : 0 < k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ f : ℕ → SchwartzMap (GlyzSpace k) ℂ,
      GlyzDyadicSupported k N f →
      lpNorm (fun x => ∑ i ∈ Finset.range (2 ^ N), f i x)
          (glyzCriticalNNExponent k) volume ^ (2 : ℕ) ≤
        C * (2 : ℝ) ^ (ε * N) *
          glyzDyadicSquareEnergy k N (glyzCriticalNNExponent k) f :=
  glyz_dyadic_decoupling_of_admissible_square_loss (one_le_glyzCriticalNNExponent hk)
    (glyz_critical_admissible_square_loss k hk hε)

end PlanarNikodym
