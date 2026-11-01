import PlanarNikodym.Analysis.Maximal.Averaging
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace PlanarNikodym

/-- A smooth low-frequency symbol, equal to one near zero and compactly
supported. Fourier reconstruction is not a field of this structure. -/
structure FrequencyCutoff where
  symbol : Plane → ℝ
  smooth : ContDiff ℝ ∞ symbol
  compact : HasCompactSupport symbol
  near_zero : ∀ ξ : Plane, ‖ξ‖ ≤ 1 → symbol ξ = 1

/-- Existence of a genuine smooth compact cutoff is unconditional. This
does not assert Fourier reconstruction or positivity of its inverse kernel. -/
def standardFrequencyCutoff : FrequencyCutoff := by
  let b : ContDiffBump (0 : Plane) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_⟩
  intro ξ hξ
  exact b.one_of_mem_closedBall (by simpa [b, mem_closedBall_zero_iff] using hξ)

def fourierPhase (x ξ : Plane) : ℝ := x.1 * ξ.1 + x.2 * ξ.2

/-- Inverse Fourier integral with the `exp(2π i x·ξ)` normalization.
The product norm on `Plane` is not treated as a Euclidean inner-product norm. -/
def inverseFourierIntegral (m : Plane → ℝ) (x : Plane) : ℂ :=
  ∫ ξ : Plane, (m ξ : ℂ) * Complex.exp
    (((2 * Real.pi * fourierPhase x ξ : ℝ) : ℂ) * Complex.I)

def FrequencyCutoff.lowSymbol (L : FrequencyCutoff) (N : ℕ) (ξ : Plane) : ℝ :=
  L.symbol (((2 : ℝ) ^ N)⁻¹ • ξ)

def FrequencyCutoff.bandSymbol (L : FrequencyCutoff) (k : ℕ) (ξ : Plane) : ℝ :=
  L.lowSymbol (k + 1) ξ - L.lowSymbol k ξ

def FrequencyCutoff.lowKernel (L : FrequencyCutoff) : Plane → ℂ :=
  inverseFourierIntegral (L.lowSymbol 0)

def FrequencyCutoff.bandKernel (L : FrequencyCutoff) (k : ℕ) : Plane → ℂ :=
  inverseFourierIntegral (L.bandSymbol k)

def FrequencyCutoff.low (L : FrequencyCutoff) (f : Plane → ℂ) (x : Plane) : ℂ :=
  ∫ y : Plane, L.lowKernel (x - y) * f y

/-- An actual convolution operator defined from the dyadic Fourier symbol,
not an arbitrary sequence of linear maps. -/
def FrequencyCutoff.band (L : FrequencyCutoff) (k : ℕ)
    (f : Plane → ℂ) (x : Plane) : ℂ :=
  ∫ y : Plane, L.bandKernel k (x - y) * f y

theorem FrequencyCutoff.finite_partition (L : FrequencyCutoff) (N : ℕ) (ξ : Plane) :
    L.lowSymbol 0 ξ + ∑ k ∈ Finset.range N, L.bandSymbol k ξ = L.lowSymbol N ξ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, bandSymbol]
    ring

@[simp] theorem FrequencyCutoff.lowSymbol_zero (L : FrequencyCutoff) (ξ : Plane) :
    L.lowSymbol 0 ξ = L.symbol ξ := by simp [lowSymbol]

theorem FrequencyCutoff.bandSymbol_smooth (L : FrequencyCutoff) (k : ℕ) :
    ContDiff ℝ ∞ (L.bandSymbol k) := by
  unfold bandSymbol lowSymbol
  have hφ := L.smooth
  fun_prop

theorem FrequencyCutoff.lowSymbol_compact (L : FrequencyCutoff) (N : ℕ) :
    HasCompactSupport (L.lowSymbol N) :=
  L.compact.comp_smul (by positivity : ((2 : ℝ) ^ N)⁻¹ ≠ 0)

theorem FrequencyCutoff.bandSymbol_compact (L : FrequencyCutoff) (k : ℕ) :
    HasCompactSupport (L.bandSymbol k) :=
  (L.lowSymbol_compact (k + 1)).sub (L.lowSymbol_compact k)

theorem FrequencyCutoff.bandSymbol_vanishes_below_scale (L : FrequencyCutoff)
    (k : ℕ) {ξ : Plane} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ k) : L.bandSymbol k ξ = 0 := by
  have hsmall (N : ℕ) (hN : ‖ξ‖ ≤ (2 : ℝ) ^ N) :
      ‖((2 : ℝ) ^ N)⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ ((2 : ℝ) ^ N)⁻¹ * (2 : ℝ) ^ N := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have hk : ‖ξ‖ ≤ (2 : ℝ) ^ (k + 1) := hξ.trans (by
    rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k])
  simp [bandSymbol, lowSymbol, L.near_zero _ (hsmall (k + 1) hk),
    L.near_zero _ (hsmall k hξ)]

theorem FrequencyCutoff.bandSymbol_vanishes_near_zero (L : FrequencyCutoff)
    (k : ℕ) {ξ : Plane} (hξ : ‖ξ‖ ≤ 1) : L.bandSymbol k ξ = 0 := by
  have hsmall (N : ℕ) : ‖((2 : ℝ) ^ N)⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hξ (by positivity)).trans (by
      simpa using inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  simp [bandSymbol, lowSymbol, L.near_zero _ (hsmall (k + 1)), L.near_zero _ (hsmall k)]

end PlanarNikodym
