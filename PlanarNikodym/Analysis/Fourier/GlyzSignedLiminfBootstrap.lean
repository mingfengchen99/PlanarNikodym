import PlanarNikodym.Analysis.Fourier.GlyzFiniteBootstrap
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.LiminfLimsup

/-! Real, bounded lower limits for the signed deviations in GLYZ §4.
The bounds are explicit: conditionally complete real infima must not silently
stand in for infinite lower limits. Positive rescaling is handled on the
right-hand neighbourhood filter before applying finite cancellation. -/
noncomputable section
open Filter Topology
namespace PlanarNikodym

/-- A bounded real lower limit respects a positive-rescaling recursion. -/
theorem glyz_liminf_scaled_recursion (F G H : ℝ → ℝ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hG : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·) G)
    (hH : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·) H)
    (hF : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) F)
    (hrec : ∀ᶠ t in 𝓝[>] (0 : ℝ), a * G (c * t) + b * H t ≤ F t) :
    a * liminf G (𝓝[>] (0 : ℝ)) + b * liminf H (𝓝[>] (0 : ℝ)) ≤
      liminf F (𝓝[>] (0 : ℝ)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (a + b + 1)
  have hd : 0 < δ := div_pos hε (by positivity)
  have hd_eq : (a + b + 1) * δ = ε := by
    dsimp [δ]
    field_simp
  have hg := eventually_nhdsGT_zero_mul_left hc
    (eventually_lt_of_lt_liminf (show liminf G (𝓝[>] (0 : ℝ)) - δ <
      liminf G (𝓝[>] (0 : ℝ)) by linarith) hG)
  have hh := eventually_lt_of_lt_liminf
    (show liminf H (𝓝[>] (0 : ℝ)) - δ <
      liminf H (𝓝[>] (0 : ℝ)) by linarith) hH
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      a * liminf G (𝓝[>] (0 : ℝ)) + b * liminf H (𝓝[>] (0 : ℝ)) - ε ≤ F t := by
    filter_upwards [hrec, hg, hh] with t ht hgt hht
    have hag := mul_le_mul_of_nonneg_left hgt.le ha
    have hbh := mul_le_mul_of_nonneg_left hht.le hb
    nlinarith
  have hlim := le_liminf_of_le hF.isCoboundedUnder_ge hev
  linarith

/-- The signed functional recursion implies zero loss once each function has
finite eventual bounds. The index zero is the constant original loss. -/
theorem glyz_signed_functional_bootstrap_zero {N : ℕ} (hN : 0 < N)
    (F : ℕ → ℝ → ℝ) (c : ℕ → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hzero : ∀ᶠ t in 𝓝[>] (0 : ℝ), F 0 t = η)
    (hbelow : ∀ i ≤ N, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·) (F i))
    (habove : ∀ i ≤ N, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) (F i))
    (hc : ∀ i < N, 0 < c i)
    (hrec : ∀ i < N, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      F (N - i) (c i * t) / ((i : ℝ) + 1) +
        ((N - i : ℕ) : ℝ) / ((N - i : ℕ) + 1 : ℝ) * F i t ≤ F (i + 1) t) :
    η = 0 := by
  let A : ℕ → ℝ := fun i => liminf (F i) (𝓝[>] (0 : ℝ))
  have hA0 : A 0 = η := by
    dsimp [A]
    rw [liminf_congr hzero, liminf_const]
  have hz := glyz_finite_bootstrap_zero hN A (by simpa [hA0] using hη)
    (fun i hi => by
      have hh := glyz_liminf_scaled_recursion (F (i + 1)) (F (N - i)) (F i)
        (a := 1 / ((i : ℝ) + 1))
        (b := ((N - i : ℕ) : ℝ) / ((N - i : ℕ) + 1 : ℝ))
        (by positivity) (by positivity) (hc i hi)
        (hbelow (N - i) (Nat.sub_le _ _)) (hbelow i (by omega))
        (habove (i + 1) (by omega))
        (by simpa only [one_div_mul_eq_div] using hrec i hi)
      simpa only [A, one_div_mul_eq_div] using hh)
  simpa [hA0] using hz

end PlanarNikodym
