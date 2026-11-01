import PlanarNikodym.Analysis.Fourier.GlyzProjectedInterpolation

/-! Finite-index transport and the critical ℓ²-to-ℓp conversion used by
the actual high-exponent moment and curve estimates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace PlanarNikodym

def glyzFinExtend {V : Type*} [Zero V] {n : ℕ} (f : Fin n → V) (i : ℕ) : V :=
  if hi : i < n then f ⟨i, hi⟩ else 0

@[simp] theorem glyzFinExtend_apply {V : Type*} [Zero V] {n : ℕ}
    (f : Fin n → V) (i : Fin n) : glyzFinExtend f i = f i := by
  simp [glyzFinExtend, i.isLt]

theorem sum_glyzFinExtend {V : Type*} [AddCommMonoid V] {n : ℕ} (f : Fin n → V) :
    ∑ i ∈ Finset.range n, glyzFinExtend f i = ∑ i, f i := by
  exact (Finset.sum_fin_eq_sum_range f).symm

theorem sum_comp_glyzFinExtend {V W : Type*} [Zero V] [AddCommMonoid W] {n : ℕ}
    (f : Fin n → V) (F : V → W) :
    ∑ i ∈ Finset.range n, F (glyzFinExtend f i) = ∑ i, F (f i) := by
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [glyzFinExtend_apply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_fintype_square_to_lp_power
    {ι : Type*} [Fintype ι] (f : ι → SchwartzMap E ℂ)
    {q : ℝ≥0} (hq : 2 ≤ q) {D : ℝ} (hD : 0 ≤ D)
    (h : lpNorm ((∑ i, f i : SchwartzMap E ℂ) : E → ℂ) q volume ^ 2 ≤
      D * ∑ i, lpNorm (f i : E → ℂ) q volume ^ 2) :
    (∫⁻ x, ENNReal.ofReal (‖(∑ i, f i : SchwartzMap E ℂ) x‖ ^ (q : ℝ))) ≤
      ENNReal.ofReal (D ^ ((q : ℝ) / 2) *
        (Fintype.card ι : ℝ) ^ ((q : ℝ) / 2 - 1)) *
          ∑ i, ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (q : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 2) hq
  have hqR : (2 : ℝ) ≤ q := hq
  have hh := glyz_fintype_square_decoupling_to_power_integrals f hq0 hD h
  have hseq := ENNReal.rpow_sum_le_const_mul_sum_rpow Finset.univ
    (fun i => (∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ)) ^ (2 / (q : ℝ)))
    (show (1 : ℝ) ≤ (q : ℝ) / 2 by linarith)
  have he : 2 / (q : ℝ) * ((q : ℝ) / 2) = 1 := by field_simp
  simp only [← ENNReal.rpow_mul, he, ENNReal.rpow_one, Finset.card_univ] at hseq
  have hh' := hh.trans (mul_le_mul' le_rfl hseq)
  have hcoef : ENNReal.ofReal D ^ ((q : ℝ) / 2) *
      ((Fintype.card ι : ℝ≥0∞) ^ ((q : ℝ) / 2 - 1) *
        ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ)) =
      ENNReal.ofReal (D ^ ((q : ℝ) / 2) *
        (Fintype.card ι : ℝ) ^ ((q : ℝ) / 2 - 1)) *
          ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ (q : ℝ) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hD _),
      ENNReal.ofReal_rpow_of_nonneg hD (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg (Fintype.card ι))
        (show 0 ≤ (q : ℝ) / 2 - 1 by linarith), ENNReal.ofReal_natCast]
    ring
  rw [hcoef] at hh'
  simpa only [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) q.coe_nonneg] using hh'

theorem glyz_dyadic_power_coefficient {q C ε d : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (N : ℕ) :
    (C * (2 : ℝ) ^ ((2 * ε / q) * N)) ^ (q / 2) *
        ((2 : ℝ) ^ N) ^ d =
      C ^ (q / 2) * (2 : ℝ) ^ ((d + ε) * N) := by
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : ((2 * ε / q) * (N : ℝ)) * (q / 2) + (N : ℝ) * d = (d + ε) * N := by
    field_simp
    ring
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), he]

end PlanarNikodym
