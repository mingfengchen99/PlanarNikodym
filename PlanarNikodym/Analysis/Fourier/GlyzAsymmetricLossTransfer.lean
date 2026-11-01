import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants

/-! Passing an arbitrarily small uniform loss between actual asymmetric
constants to their optimal growth exponents. Infima are approximated
from above; no attainment of an optimal exponent is assumed. -/
noncomputable section
open scoped NNReal
namespace PlanarNikodym

theorem glyz_admissible_asymmetric_loss_of_comparison
    {m A : ℕ} {p : ℝ≥0} {a α β α' β' e ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 0 < C)
    (hcompare : ∀ N : ℕ,
      glyzAsymmetricIntegralConstant m A N (glyzDyadicDepth N α)
        (glyzDyadicDepth N β) p a ≤ C * (2 : ℝ) ^ (ε * N) *
          glyzAsymmetricIntegralConstant m A N (glyzDyadicDepth N α')
            (glyzDyadicDepth N β') p a)
    (he : GlyzAdmissibleAsymmetricLoss m A p a α' β' e) :
    GlyzAdmissibleAsymmetricLoss m A p a α β (e + ε) := by
  obtain ⟨he0, B, hB, hbound⟩ := he
  refine ⟨add_nonneg he0 hε, C * B, mul_pos hC hB, fun N => ?_⟩
  apply (hcompare N).trans
  apply (mul_le_mul_of_nonneg_left (hbound N) (by positivity)).trans_eq
  calc
    _ = (C * B) * ((2 : ℝ) ^ (e * N) * (2 : ℝ) ^ (ε * N)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

theorem glyzOptimalAsymmetricLoss_le_of_small_loss_comparison
    {m A : ℕ} (hA : m < A) (p : ℝ≥0) (hp : 1 ≤ p)
    {a α β α' β' : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ))
    (hcompare : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      glyzAsymmetricIntegralConstant m A N (glyzDyadicDepth N α)
        (glyzDyadicDepth N β) p a ≤ C * (2 : ℝ) ^ (ε * N) *
          glyzAsymmetricIntegralConstant m A N (glyzDyadicDepth N α')
            (glyzDyadicDepth N β') p a) :
    glyzOptimalAsymmetricLoss m A p a α β ≤ glyzOptimalAsymmetricLoss m A p a α' β' := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, hC, hcompare⟩ := hcompare (ε / 2) (by positivity)
  have he := glyz_admissible_asymmetric_loss_of_optimal_lt hA p hp ha hap α' β'
    (show glyzOptimalAsymmetricLoss m A p a α' β' <
      glyzOptimalAsymmetricLoss m A p a α' β' + ε / 2 by linarith)
  have h := glyzOptimalAsymmetricLoss_le
    (glyz_admissible_asymmetric_loss_of_comparison (by positivity) hC hcompare he)
  exact h.trans_eq (by ring)

end PlanarNikodym
