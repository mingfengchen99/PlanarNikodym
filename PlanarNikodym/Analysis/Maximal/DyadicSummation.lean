import PlanarNikodym.Analysis.Maximal.Averaging
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

/-- `2^(a k)`, written as a geometric sequence to expose summability. -/
def dyadicWeight (a : ℝ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ a) ^ k

theorem dyadicWeight_add (a b : ℝ) (k : ℕ) :
    dyadicWeight (a + b) k = dyadicWeight a k * dyadicWeight b k := by
  unfold dyadicWeight
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a), mul_pow]

theorem dyadicWeight_tsum_lt_top {a : ℝ} (ha : a < 0) :
    (∑' k, dyadicWeight a k) < ∞ := by
  have hpos : 0 ≤ (2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have hlt : |(2 : ℝ) ^ a| < 1 := by
    rw [abs_of_nonneg hpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha
  have hs := summable_geometric_of_abs_lt_one hlt
  have he : (∑' k, dyadicWeight a k) = ENNReal.ofReal (∑' k, ((2 : ℝ) ^ a) ^ k) := by
    simp only [dyadicWeight, ← ENNReal.ofReal_pow hpos]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => pow_nonneg hpos _) hs).symm
  rw [he]
  exact ENNReal.ofReal_lt_top

theorem eLpNorm_iSup_nonnegative {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ≥0) (hp : 0 < p)
    (f : ℕ → X → ℝ≥0∞) (hm : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    eLpNorm (fun x => ⨆ n, f n x) p μ = ⨆ n, eLpNorm (f n) p μ := by
  have hpR : 0 < (p : ℝ) := hp
  simp only [eLpNorm_nnreal_eq_lintegral hp.ne', enorm_eq_self]
  have hr (x : X) : (⨆ n, f n x) ^ (p : ℝ) = ⨆ n, f n x ^ (p : ℝ) :=
    (ENNReal.orderIsoRpow (p : ℝ) hpR).map_iSup _
  simp_rw [hr]
  rw [lintegral_iSup (fun n => (hm n).pow_const _)
    (fun i j hij x => ENNReal.rpow_le_rpow (hmono hij x) hpR.le)]
  exact (ENNReal.orderIsoRpow (1 / (p : ℝ)) (one_div_pos.mpr hpR)).map_iSup _

/-- Infinite Minkowski for extended-valued nonnegative majorants. This
handles pointwise suprema without choosing an a.e. finite representative. -/
theorem eLpNorm_tsum_nonnegative_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ≥0) (hp : 1 ≤ p)
    (f : ℕ → X → ℝ≥0∞) (hm : ∀ n, Measurable (f n)) :
    eLpNorm (fun x => ∑' n, f n x) p μ ≤ ∑' n, eLpNorm (f n) p μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let S : ℕ → X → ℝ≥0∞ := fun n x => ∑ k ∈ Finset.range n, f k x
  have hmS (n : ℕ) : Measurable (S n) :=
    Finset.measurable_sum _ (fun k _ => hm k)
  have hmonoS : Monotone S := fun i j hij x =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hij)
  have he : (fun x => ∑' k, f k x) = fun x => ⨆ n, S n x := by
    funext x
    exact ENNReal.tsum_eq_iSup_nat
  rw [he, eLpNorm_iSup_nonnegative μ p hp0 S hmS hmonoS]
  apply iSup_le
  intro n
  have hs := eLpNorm_sum_le (μ := μ) (f := f) (s := Finset.range n) (p := (p : ℝ≥0∞))
    (fun k _ => (hm k).stronglyMeasurable.aestronglyMeasurable)
    (by exact_mod_cast hp)
  have hs' : eLpNorm (S n) p μ ≤ ∑ k ∈ Finset.range n, eLpNorm (f k) p μ := by
    have hfun : S n = ∑ k ∈ Finset.range n, f k := by ext x; simp [S]
    rw [hfun]
    exact hs
  exact hs'.trans (ENNReal.sum_le_tsum (Finset.range n))

/-- The summation step used after Corollary 2.2. Reconstruction is a
separate pointwise hypothesis; no convergence on curves is inferred merely
from convergence in ambient `Lp`. -/
theorem dyadic_majorant_estimate {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ≥0) (hp : 1 ≤ p)
    (F : X → ℝ≥0∞) (b : ℕ → X → ℝ≥0∞)
    (hm : ∀ k, Measurable (b k)) (hF : ∀ x, F x ≤ ∑' k, b k x)
    (a : ℝ) (C N : ℝ≥0∞)
    (hb : ∀ k, eLpNorm (b k) p μ ≤ C * dyadicWeight a k * N) :
    eLpNorm F p μ ≤ (C * ∑' k, dyadicWeight a k) * N := by
  calc
    _ ≤ eLpNorm (fun x => ∑' k, b k x) p μ :=
      eLpNorm_mono_enorm (by simpa only [enorm_eq_self] using hF)
    _ ≤ ∑' k, eLpNorm (b k) p μ := eLpNorm_tsum_nonnegative_le μ p hp b hm
    _ ≤ ∑' k, C * dyadicWeight a k * N := ENNReal.tsum_le_tsum hb
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

end PlanarNikodym
