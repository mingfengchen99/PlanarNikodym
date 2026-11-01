import PlanarNikodym.Analysis.Fourier.GlyzAsymmetricConstants
import PlanarNikodym.Analysis.Fourier.GlyzDyadicOptimalRescaling

/-! The upper comparison (4.6) between actual asymmetric and linear
decoupling exponents. Affine rescaling and Hölder supply the two
relative-depth constants; rounding the parent depths introduces no
additional exponent. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace PlanarNikodym

theorem glyz_asymmetric_integral_bound_of_linear_constants {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (hn : n ≤ N) (hn' : n' ≤ N) (p : ℝ≥0) (hp : 1 ≤ p)
    {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) :
    GlyzAsymmetricIntegralBound m A N n n' p a
      (glyzPolarMass m A ^ (2 : ℕ) *
        (glyzDyadicSquareConstant m (N - n) p ^ (a / 2) *
          glyzDyadicSquareConstant m (N - n') p ^ (((p : ℝ) - a) / 2))) := by
  have hD := glyzDyadicSquareConstant_nonneg m (N - n) p hp
  have hD' := glyzDyadicSquareConstant_nonneg m (N - n') p hp
  refine ⟨mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg hD _)
    (Real.rpow_nonneg hD' _)), fun f hf i hi j hj _ => ?_⟩
  have h := glyz_polar_bilinear_toReal_le_sq_lpNorm_bounds hA
    (glyzMomentFrequencyFrame m (glyzDyadicCenter n i) (glyzDyadicScale n)
      (glyzDyadicScale_pos n))
    (glyzMomentFrequencyFrame m (glyzDyadicCenter n' j) (glyzDyadicScale n')
      (glyzDyadicScale_pos n'))
    (glyzDyadicBlock f N n i) (glyzDyadicBlock f N n' j)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hp) ha hap
    (glyz_dyadic_block_le_optimal_constant m N n i hn hi p hp f hf)
    (glyz_dyadic_block_le_optimal_constant m N n' j hn' hj p hp f hf)
  apply h.trans_eq
  rw [Real.mul_rpow hD (glyz_dyadic_square_block_nonneg m N n i p f),
    Real.mul_rpow hD' (glyz_dyadic_square_block_nonneg m N n' j p f)]
  unfold glyzDyadicBilinearEnergy
  ring

theorem glyzAsymmetricIntegralConstant_le_linear_constants {m A : ℕ} (hA : m < A)
    (N n n' : ℕ) (hn : n ≤ N) (hn' : n' ≤ N) (p : ℝ≥0) (hp : 1 ≤ p)
    {a : ℝ} (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) :
    glyzAsymmetricIntegralConstant m A N n n' p a ≤
      glyzPolarMass m A ^ (2 : ℕ) *
        (glyzDyadicSquareConstant m (N - n) p ^ (a / 2) *
          glyzDyadicSquareConstant m (N - n') p ^ (((p : ℝ) - a) / 2)) :=
  glyzAsymmetricIntegralConstant_le
    (glyz_asymmetric_integral_bound_of_linear_constants hA N n n' hn hn' p hp ha hap)

theorem glyzDyadicDepth_remainder_le (N : ℕ) {alpha : ℝ} (ha : alpha ≤ 1) :
    ((N - glyzDyadicDepth N alpha : ℕ) : ℝ) ≤ (1 - alpha) * N := by
  rw [Nat.cast_sub (glyzDyadicDepth_le ha)]
  have h := Nat.le_ceil (alpha * N)
  change alpha * N ≤ (glyzDyadicDepth N alpha : ℝ) at h
  nlinarith

def glyzAsymmetricLinearLossFactor (p : ℝ≥0) (a alpha beta : ℝ) : ℝ :=
  (1 - alpha) * (a / 2) + (1 - beta) * (((p : ℝ) - a) / 2)

theorem glyzAsymmetricLinearLossFactor_nonneg {p : ℝ≥0} {a alpha beta : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) (halpha : alpha ≤ 1) (hbeta : beta ≤ 1) :
    0 ≤ glyzAsymmetricLinearLossFactor p a alpha beta :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr halpha) (by positivity))
    (mul_nonneg (sub_nonneg.mpr hbeta) (by positivity))

theorem glyz_admissible_asymmetric_loss_of_linear {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a alpha beta e : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) (halpha : alpha ≤ 1) (hbeta : beta ≤ 1)
    (he : GlyzAdmissibleSquareLoss m p e) :
    GlyzAdmissibleAsymmetricLoss m A p a alpha beta
      (e * glyzAsymmetricLinearLossFactor p a alpha beta) := by
  obtain ⟨he, C, hC, h⟩ := he
  have hF := glyzAsymmetricLinearLossFactor_nonneg ha hap halpha hbeta
  refine ⟨mul_nonneg he hF, glyzPolarMass m A ^ (2 : ℕ) * C ^ ((p : ℝ) / 2),
    mul_pos (sq_pos_of_pos (glyzPolarMass_pos hA)) (Real.rpow_pos_of_pos hC _), fun N => ?_⟩
  have hD (t : ℝ) (ht : t ≤ 1) :
      glyzDyadicSquareConstant m (N - glyzDyadicDepth N t) p ≤
        C * (2 : ℝ) ^ (e * (1 - t) * N) := by
    apply (h (N - glyzDyadicDepth N t)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left (glyzDyadicDepth_remainder_le N ht) he]
  have hD₁ := Real.rpow_le_rpow
    (glyzDyadicSquareConstant_nonneg m (N - glyzDyadicDepth N alpha) p hp)
    (hD alpha halpha) (show 0 ≤ a / 2 by positivity)
  have hD₂ := Real.rpow_le_rpow
    (glyzDyadicSquareConstant_nonneg m (N - glyzDyadicDepth N beta) p hp)
    (hD beta hbeta) (show 0 ≤ ((p : ℝ) - a) / 2 by positivity)
  apply (glyzAsymmetricIntegralConstant_le_linear_constants hA N
    (glyzDyadicDepth N alpha) (glyzDyadicDepth N beta)
    (glyzDyadicDepth_le halpha) (glyzDyadicDepth_le hbeta) p hp ha hap).trans
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hD₁ hD₂
    (Real.rpow_nonneg (glyzDyadicSquareConstant_nonneg m _ p hp) _)
    (Real.rpow_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _)) _))
    (sq_nonneg (glyzPolarMass m A))).trans_eq
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg (by norm_num) _),
    Real.mul_rpow hC.le (Real.rpow_nonneg (by norm_num) _)]
  have hCpow : C ^ (a / 2) * C ^ (((p : ℝ) - a) / 2) = C ^ ((p : ℝ) / 2) := by
    rw [← Real.rpow_add hC]
    congr 1
    ring
  have h2pow : ((2 : ℝ) ^ (e * (1 - alpha) * N)) ^ (a / 2) *
      ((2 : ℝ) ^ (e * (1 - beta) * N)) ^ (((p : ℝ) - a) / 2) =
        (2 : ℝ) ^ (e * glyzAsymmetricLinearLossFactor p a alpha beta * N) := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    unfold glyzAsymmetricLinearLossFactor
    ring
  calc
    _ = glyzPolarMass m A ^ (2 : ℕ) *
        (C ^ (a / 2) * C ^ (((p : ℝ) - a) / 2)) *
        (((2 : ℝ) ^ (e * (1 - alpha) * N)) ^ (a / 2) *
          ((2 : ℝ) ^ (e * (1 - beta) * N)) ^ (((p : ℝ) - a) / 2)) := by ring
    _ = _ := by rw [hCpow, h2pow]

/-- Formula (4.6), with squared linear constants and `p`-powered
bilinear constants. It bounds the genuine optimal exponent, not an
arbitrarily postulated exponent function. -/
theorem glyzOptimalAsymmetricLoss_le_linear {m A : ℕ} (hA : m < A)
    (p : ℝ≥0) (hp : 1 ≤ p) {a alpha beta : ℝ}
    (ha : 0 ≤ a) (hap : a ≤ (p : ℝ)) (halpha : alpha ≤ 1) (hbeta : beta ≤ 1) :
    glyzOptimalAsymmetricLoss m A p a alpha beta ≤
      glyzOptimalSquareLoss m p * glyzAsymmetricLinearLossFactor p a alpha beta := by
  have hF := glyzAsymmetricLinearLossFactor_nonneg ha hap halpha hbeta
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < glyzAsymmetricLinearLossFactor p a alpha beta + 1 := by linarith
  have he := glyz_admissible_square_loss_add_epsilon m p hp (div_pos hε hden)
  have h := glyzOptimalAsymmetricLoss_le
    (glyz_admissible_asymmetric_loss_of_linear hA p hp ha hap halpha hbeta he)
  apply h.trans
  have heF : ε / (glyzAsymmetricLinearLossFactor p a alpha beta + 1) *
      glyzAsymmetricLinearLossFactor p a alpha beta ≤ ε := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  nlinarith

end PlanarNikodym
