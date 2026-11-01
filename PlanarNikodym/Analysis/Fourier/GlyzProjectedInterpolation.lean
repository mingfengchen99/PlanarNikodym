import PlanarNikodym.Analysis.Fourier.GlyzFourierProjector
import PlanarNikodym.Analysis.Fourier.GlyzSchwartzInterpolation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! From a genuine critical estimate for the projected pieces to the
supercritical ℓp estimate. The operator is the sum of the actual Fourier
projections; every endpoint estimate is checked on arbitrary Schwartz
inputs before interpolation. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_fintype_square_decoupling_to_power_integrals
    {ι : Type*} [Fintype ι] (f : ι → SchwartzMap E ℂ)
    {q : ℝ≥0} (hq : 0 < q) {D : ℝ} (hD : 0 ≤ D)
    (h : lpNorm ((∑ i, f i : SchwartzMap E ℂ) : E → ℂ) q volume ^ 2 ≤
      D * ∑ i, lpNorm (f i : E → ℂ) q volume ^ 2) :
    (∫⁻ x, ‖(∑ i, f i : SchwartzMap E ℂ) x‖ₑ ^ (q : ℝ)) ≤
      ENNReal.ofReal D ^ ((q : ℝ) / 2) *
        (∑ i, (∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ)) ^ (2 / (q : ℝ))) ^ ((q : ℝ) / 2) := by
  have hqR : (0 : ℝ) < q := hq
  have hs : eLpNorm ((∑ i, f i : SchwartzMap E ℂ) : E → ℂ) q volume ^ (2 : ℕ) ≤
      ENNReal.ofReal (D * ∑ i, lpNorm (f i : E → ℂ) q volume ^ 2) := by
    rw [← ofReal_lpNorm ((∑ i, f i : SchwartzMap E ℂ).memLp q volume),
      ← ENNReal.ofReal_pow lpNorm_nonneg]
    exact ENNReal.ofReal_le_ofReal h
  have hh := ENNReal.rpow_le_rpow hs (show 0 ≤ (q : ℝ) / 2 by positivity)
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat,
    show (2 : ℝ) * ((q : ℝ) / 2) = q by ring,
    eLpNorm_nnreal_pow_eq_lintegral hq.ne', ENNReal.ofReal_mul hD,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at hh
  have hi (i : ι) : ENNReal.ofReal (lpNorm (f i : E → ℂ) q volume ^ (2 : ℕ)) =
      (∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ)) ^ (2 / (q : ℝ)) := by
    rw [← eLpNorm_nnreal_pow_eq_lintegral hq.ne', ← ENNReal.rpow_mul,
      show (q : ℝ) * (2 / (q : ℝ)) = 2 by field_simp,
      ENNReal.rpow_two, ← ofReal_lpNorm ((f i).memLp q volume),
      ENNReal.ofReal_pow lpNorm_nonneg]
  simpa only [hi] using hh

theorem glyzProjectionSum_critical_power_bound
    {ι : Type*} [Fintype ι] (χ : ι → SchwartzMap E ℂ)
    {q : ℝ≥0} (hq : 2 ≤ q) {D M : ℝ} (hD : 0 ≤ D) (hM0 : 0 ≤ M)
    (hM : ∀ i, (∫ x, ‖glyzReproducingKernel (χ i) x‖) ≤ M)
    (hcrit : ∀ g : ι → SchwartzMap E ℂ,
      lpNorm (glyzProjectionSum χ g : E → ℂ) q volume ^ 2 ≤
        D * ∑ i, lpNorm (glyzFourierProjector (χ i) (g i) : E → ℂ) q volume ^ 2)
    (f : ι → SchwartzMap E ℂ) :
    (∫⁻ x, ENNReal.ofReal (‖glyzProjectionSum χ f x‖ ^ (q : ℝ))) ≤
      ENNReal.ofReal (D ^ ((q : ℝ) / 2) *
        (Fintype.card ι : ℝ) ^ ((q : ℝ) / 2 - 1) * M ^ (q : ℝ)) *
          ∑ i, ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (q : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 2) hq
  have hq1 : 1 ≤ q := (by norm_num : (1 : ℝ≥0) ≤ 2).trans hq
  let P := fun i => glyzFourierProjector (χ i) (f i)
  have hcrit' : lpNorm ((∑ i, P i : SchwartzMap E ℂ) : E → ℂ) q volume ^ 2 ≤
      D * ∑ i, lpNorm (P i : E → ℂ) q volume ^ 2 := by
    simpa only [glyzProjectionSum_apply, P] using hcrit f
  have h := glyz_fintype_square_decoupling_to_power_integrals P hq0 hD hcrit'
  have hseq := ENNReal.rpow_sum_le_const_mul_sum_rpow Finset.univ
    (fun i => (∫⁻ x, ‖P i x‖ₑ ^ (q : ℝ)) ^ (2 / (q : ℝ)))
    (show (1 : ℝ) ≤ (q : ℝ) / 2 by
      have hqR : (2 : ℝ) ≤ q := hq
      linarith)
  have he : 2 / (q : ℝ) * ((q : ℝ) / 2) = 1 := by field_simp
  simp only [← ENNReal.rpow_mul, he, ENNReal.rpow_one, Finset.card_univ] at hseq
  have hsum :
      (∑ i, ∫⁻ x, ‖P i x‖ₑ ^ (q : ℝ)) ≤
        ENNReal.ofReal M ^ (q : ℝ) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ) := by
    calc
      _ ≤ ∑ i, ENNReal.ofReal M ^ (q : ℝ) * ∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ) :=
        Finset.sum_le_sum fun i _ =>
          glyzFourierProjector_power_integral_le (χ i) (f i) hq1 hM0 (hM i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hh := h.trans (mul_le_mul' le_rfl
    (hseq.trans (mul_le_mul' le_rfl hsum)))
  have hcoef : ENNReal.ofReal D ^ ((q : ℝ) / 2) *
      ((Fintype.card ι : ℝ≥0∞) ^ ((q : ℝ) / 2 - 1) *
        (ENNReal.ofReal M ^ (q : ℝ) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ))) =
      ENNReal.ofReal (D ^ ((q : ℝ) / 2) *
        (Fintype.card ι : ℝ) ^ ((q : ℝ) / 2 - 1) * M ^ (q : ℝ)) *
          ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hD _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)),
      ENNReal.ofReal_mul (Real.rpow_nonneg hD _),
      ENNReal.ofReal_rpow_of_nonneg hD (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg (Fintype.card ι))
        (show 0 ≤ (q : ℝ) / 2 - 1 by
        have hqR : (2 : ℝ) ≤ q := hq
        linarith),
      ENNReal.ofReal_rpow_of_nonneg hM0 q.coe_nonneg,
      ENNReal.ofReal_natCast]
    ring
  rw [hcoef] at hh
  simpa only [glyzProjectionSum_apply, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) q.coe_nonneg, P] using hh

def glyzInterpolationFactor (p q : ℝ) : ℝ :=
  p * (2 : ℝ) ^ q * (4 : ℝ) ^ (p - q) / (p - q)

theorem glyzInterpolationFactor_pos {p q : ℝ} (hq : 0 < q) (hpq : q < p) :
    0 < glyzInterpolationFactor p q := by
  unfold glyzInterpolationFactor
  exact div_pos (mul_pos (mul_pos (hq.trans hpq) (by positivity)) (by positivity)) (sub_pos.mpr hpq)

theorem glyz_interpolation_coefficient {p q D M c : ℝ}
    (_hD : 0 ≤ D) (hM : 0 < M) (hc : 0 < c) :
    p * (2 : ℝ) ^ q * (D ^ (q / 2) * c ^ (q / 2 - 1) * M ^ q) *
        (4 * (c * M)) ^ (p - q) / (p - q) =
      glyzInterpolationFactor p q * D ^ (q / 2) * c ^ (p - q / 2 - 1) * M ^ p := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_nonneg hc.le hM.le),
    Real.mul_rpow hc.le hM.le]
  have hc' : c ^ (q / 2 - 1) * c ^ (p - q) = c ^ (p - q / 2 - 1) := by
    rw [← Real.rpow_add hc]
    congr 1
    ring
  have hM' : M ^ q * M ^ (p - q) = M ^ p := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  unfold glyzInterpolationFactor
  calc
    _ = (p * (2 : ℝ) ^ q * (4 : ℝ) ^ (p - q) / (p - q)) * D ^ (q / 2) *
        (c ^ (q / 2 - 1) * c ^ (p - q)) * (M ^ q * M ^ (p - q)) := by ring
    _ = _ := by rw [hc', hM']

/-- A Fourier-projection version with the sharp ℓp cardinality exponent.
The critical estimate is checked on all projected Schwartz inputs. -/
theorem glyz_projected_supercritical_decoupling
    {ι : Type*} [Fintype ι] [Nonempty ι] (χ : ι → SchwartzMap E ℂ)
    {q : ℝ≥0} (hq : 2 ≤ q) {p D M : ℝ} (hpq : (q : ℝ) < p)
    (hD : 0 ≤ D) (hM0 : 0 < M)
    (hM : ∀ i, (∫ x, ‖glyzReproducingKernel (χ i) x‖) ≤ M)
    (hcrit : ∀ g : ι → SchwartzMap E ℂ,
      lpNorm (glyzProjectionSum χ g : E → ℂ) q volume ^ 2 ≤
        D * ∑ i, lpNorm (glyzFourierProjector (χ i) (g i) : E → ℂ) q volume ^ 2)
    (f : ι → SchwartzMap E ℂ)
    (hf : ∀ i ξ, ξ ∈ Function.support (𝓕 (f i : E → ℂ)) → χ i ξ = 1) :
    (∫⁻ x, ENNReal.ofReal (‖(∑ i, f i : SchwartzMap E ℂ) x‖ ^ p)) ≤
      ENNReal.ofReal (glyzInterpolationFactor p q * D ^ ((q : ℝ) / 2) *
        (Fintype.card ι : ℝ) ^ (p - (q : ℝ) / 2 - 1) * M ^ p) *
          ∑ i, ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ p) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hq
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := glyz_schwartz_q_infinity_interpolation (glyzProjectionSum χ) hq0 hpq
    (show 0 ≤ D ^ ((q : ℝ) / 2) * (Fintype.card ι : ℝ) ^ ((q : ℝ) / 2 - 1) *
      M ^ (q : ℝ) by positivity) (mul_pos hc hM0)
    (glyzProjectionSum_critical_power_bound χ hq hD hM0.le hM hcrit)
    (fun g B hB hg x => glyzProjectionSum_norm_le χ hB hM g hg x) f
  rw [glyz_interpolation_coefficient hD hM0 hc] at h
  have he : glyzProjectionSum χ f = ∑ i, f i := by
    rw [glyzProjectionSum_apply]
    exact Finset.sum_congr rfl fun i _ => glyzFourierProjector_reproduces (χ i) (f i) (hf i)
  simpa only [he] using h

end PlanarNikodym
