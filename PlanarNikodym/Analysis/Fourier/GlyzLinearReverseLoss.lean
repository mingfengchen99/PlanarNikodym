import PlanarNikodym.Analysis.Fourier.GlyzWhitneyBilinearTransfer
import PlanarNikodym.Analysis.Fourier.GlyzGeometricReduction

/-! The actual reverse optimal-exponent bound in GLYZ (4.7).
The proof constructs the rescaled Whitney families, uses the actual
asymmetric constants, and sums all generations. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace PlanarNikodym

theorem glyz_admissible_square_loss_of_asymmetric
    {m A : ℕ} (hA : m < A) (p : ℝ≥0) (hp : 2 ≤ p)
    {a alpha beta e : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ (p : ℝ) - a)
    (hα : 0 < alpha) (hβ : 0 < beta) (hα1 : alpha ≤ 1) (hβ1 : beta ≤ 1)
    (he : GlyzAdmissibleAsymmetricLoss m A p a alpha beta e) :
    GlyzAdmissibleSquareLoss m p
      ((2 / (p : ℝ)) * (a * alpha + ((p : ℝ) - a) * beta + e)) := by
  obtain ⟨C, hC, hfixed⟩ := glyz_fixed_depth_bilinear_of_admissible_asymmetric_loss
    hA p ha hb hα hβ hα1 hβ1 he 2
  let s : ℝ := (2 / (p : ℝ)) * (a * alpha + ((p : ℝ) - a) * beta + e)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 2) hp
  have he0 := he.1
  have hs : 0 < s := by
    dsimp only [s]
    have hpa : 0 < (p : ℝ) - a := zero_lt_one.trans_le hb
    have ha0 : 0 < a := zero_lt_one.trans_le ha
    have hpR : 0 < (p : ℝ) := hp0
    positivity
  let ρ : ℝ := (2 : ℝ) ^ s
  let K : ℝ := C * (2 : ℝ) ^ (2 * s)
  have hρ : 1 < ρ := Real.one_lt_rpow (by norm_num) hs
  have hK : 0 < K := by dsimp only [K]; positivity
  let D : ℝ := 6 + 8 * K * (ρ / (ρ - 1))
  have hD : 0 < D := by
    have hd : 0 < ρ - 1 := by linarith
    dsimp only [D]
    positivity
  refine ⟨hs.le, D, hD, fun N => glyzDyadicSquareConstant_le ⟨by positivity, fun f hf => ?_⟩⟩
  have hgeom := glyz_bilinear_to_linear_geometric f N p hp hK.le hρ
    (fun n hn i hi j hj hij => ?_)
  · have heq : ρ ^ N = (2 : ℝ) ^ (s * N) := by
      dsimp only [ρ]
      rw [← Real.rpow_natCast ((2 : ℝ) ^ s) N,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simpa only [heq, D, glyzDyadicSquareEnergy] using hgeom
  · have hpair := glyz_whitney_pair_of_fixed_depth m N (n + 1) (by omega)
      p hp0 hC.le hfixed f hf hi hj hij
    apply hpair.trans
    apply mul_le_mul_of_nonneg_right _ (add_nonneg
      (glyz_dyadic_square_block_nonneg m N _ _ p f)
      (glyz_dyadic_square_block_nonneg m N _ _ p f))
    have hcoef : (2 : ℝ) ^ (s * ((N - (n + 1) + 2 : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (2 * s) * ρ ^ (N - n) := by
      have hnat : N - (n + 1) + 2 ≤ (N - n) + 2 := by omega
      have hcast : ((N - (n + 1) + 2 : ℕ) : ℝ) ≤ ((N - n : ℕ) : ℝ) + 2 := by
        exact_mod_cast hnat
      calc
        _ ≤ (2 : ℝ) ^ (s * (((N - n : ℕ) : ℝ) + 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left hcast hs.le)
        _ = _ := by
          dsimp only [ρ]
          rw [← Real.rpow_natCast ((2 : ℝ) ^ s) (N - n),
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
    have hh := mul_le_mul_of_nonneg_left hcoef hC.le
    simpa only [K, s, mul_assoc] using hh

/-- D-squared loss is bounded by the B-to-the-p loss with exactly the
factor `2/p`. All objects are the actual Fourier-supported constants. -/
theorem glyzOptimalSquareLoss_le_asymmetric
    {m A : ℕ} (hA : m < A) (p : ℝ≥0) (hp : 2 ≤ p)
    {a alpha beta : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ (p : ℝ) - a)
    (hα : 0 < alpha) (hβ : 0 < beta) (hα1 : alpha ≤ 1) (hβ1 : beta ≤ 1) :
    glyzOptimalSquareLoss m p ≤ (2 / (p : ℝ)) *
      (a * alpha + ((p : ℝ) - a) * beta + glyzOptimalAsymmetricLoss m A p a alpha beta) := by
  have hp0 : 0 < (p : ℝ) := by
    have hp' : (2 : ℝ) ≤ p := hp
    linarith
  have hp₁ : 1 ≤ p := (by norm_num : (1 : ℝ≥0) ≤ 2).trans hp
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpert : 0 < ε * (p : ℝ) / 2 := by positivity
  have he := glyz_admissible_asymmetric_loss_of_optimal_lt hA p hp₁
    (zero_le_one.trans ha) (show a ≤ (p : ℝ) by linarith) alpha beta
    (lt_add_of_pos_right _ hpert)
  have hh := glyzOptimalSquareLoss_le
    (glyz_admissible_square_loss_of_asymmetric hA p hp ha hb hα hβ hα1 hβ1 he)
  apply hh.trans_eq
  field_simp
  ring

end PlanarNikodym
