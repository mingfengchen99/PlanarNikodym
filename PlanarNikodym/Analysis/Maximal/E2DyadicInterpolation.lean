import PlanarNikodym.Analysis.Maximal.E2BandInterpolation
import PlanarNikodym.Analysis.Maximal.DyadicSummation

/-! Quantitative dyadic decay from two finite endpoint estimates.
Every constant is chosen before the frequency and input. The hypothesis
on the endpoints is explicit; this module does not assert E1. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem e2_dyadicWeight_eq (a : ℝ) (k : ℕ) :
    dyadicWeight a k = ENNReal.ofReal ((2 : ℝ) ^ (a * k)) := by
  unfold dyadicWeight
  rw [← ENNReal.ofReal_pow (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem e2_dyadic_interpolation_coefficient
    {p q₀ q₁ C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (a₀ a₁ b : ℝ) (k : ℕ) :
    p * ((2 : ℝ) ^ q₀ * (C₀ * (2 : ℝ) ^ (a₀ * k)) ^ q₀ *
        ((2 : ℝ) ^ (b * k)) ^ (p - q₀) / (p - q₀) +
      (2 : ℝ) ^ q₁ * (C₁ * (2 : ℝ) ^ (a₁ * k)) ^ q₁ *
        ((2 : ℝ) ^ (b * k)) ^ (p - q₁) / (q₁ - p)) =
      (p * (2 : ℝ) ^ q₀ * C₀ ^ q₀ / (p - q₀)) *
          (2 : ℝ) ^ ((a₀ * q₀ + b * (p - q₀)) * k) +
      (p * (2 : ℝ) ^ q₁ * C₁ ^ q₁ / (q₁ - p)) *
          (2 : ℝ) ^ ((a₁ * q₁ + b * (p - q₁)) * k) := by
  rw [Real.mul_rpow hC₀ (by positivity), Real.mul_rpow hC₁ (by positivity),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (a₀ * q₀ + b * (p - q₀)) * (k : ℝ) =
      (a₀ * k) * q₀ + (b * k) * (p - q₀) by ring,
    show (a₁ * q₁ + b * (p - q₁)) * (k : ℝ) =
      (a₁ * k) * q₁ + (b * k) * (p - q₁) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring

theorem Family.cutoffMaximal_band_dyadic_interpolation_e2 {d : ℕ} (G : Family 2 d)
    (χ : Cutoff d) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hγ : ∀ x ∈ tsupport χ, ContinuousAt (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) x)
    (L : FrequencyCutoff) {p q₀ q₁ C₀ C₁ a₀ a₁ b a : ℝ}
    (hq₀ : 0 < q₀) (hqp : q₀ < p) (hpq : p < q₁)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (he₀ : a₀ * q₀ + b * (p - q₀) ≤ a * p)
    (he₁ : a₁ * q₁ + b * (p - q₁) ≤ a * p)
    (hlo : ∀ k : ℕ, ∀ g : Plane → ℂ, Integrable g → MemLp g (ENNReal.ofReal q₀) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k g)) (ENNReal.ofReal q₀) volume ≤
        ENNReal.ofReal C₀ * dyadicWeight a₀ k * eLpNorm g (ENNReal.ofReal q₀) volume)
    (hhi : ∀ k : ℕ, ∀ g : Plane → ℂ, Integrable g → MemLp g (ENNReal.ofReal q₁) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k g)) (ENNReal.ofReal q₁) volume ≤
        ENNReal.ofReal C₁ * dyadicWeight a₁ k * eLpNorm g (ENNReal.ofReal q₁) volume) :
    ∃ C : ℝ≥0, ∀ k : ℕ, ∀ f : Plane → ℂ, Integrable f → MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (G.cutoffMaximal χ (L.band k f)) (ENNReal.ofReal p) volume ≤
        C * dyadicWeight a k * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp : 0 < p := hq₀.trans hqp
  let D₀ : ℝ := p * (2 : ℝ) ^ q₀ * C₀ ^ q₀ / (p - q₀)
  let D₁ : ℝ := p * (2 : ℝ) ^ q₁ * C₁ ^ q₁ / (q₁ - p)
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD₁ : 0 ≤ D₁ := by dsimp [D₁]; positivity
  refine ⟨⟨(D₀ + D₁) ^ (1 / p), Real.rpow_nonneg (add_nonneg hD₀ hD₁) _⟩, ?_⟩
  intro k f hf hfp
  have hb := G.cutoffMaximal_band_finite_interpolation_e2 χ hχ hc hγ L k hq₀ hqp hpq
    (mul_nonneg hC₀ (by positivity)) (mul_nonneg hC₁ (by positivity))
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (b * k))
    (C₀ := C₀ * (2 : ℝ) ^ (a₀ * k)) (C₁ := C₁ * (2 : ℝ) ^ (a₁ * k))
    (B := (2 : ℝ) ^ (b * k))
    (fun g hg hgp => by
      simpa only [e2_dyadicWeight_eq, ENNReal.ofReal_mul hC₀, mul_assoc]
        using hlo k g hg hgp)
    (fun g hg hgp => by
      simpa only [e2_dyadicWeight_eq, ENNReal.ofReal_mul hC₁, mul_assoc]
        using hhi k g hg hgp) hf hfp
  rw [e2_dyadic_interpolation_coefficient hC₀ hC₁] at hb
  have hcoeff : D₀ * (2 : ℝ) ^ ((a₀ * q₀ + b * (p - q₀)) * k) +
      D₁ * (2 : ℝ) ^ ((a₁ * q₁ + b * (p - q₁)) * k) ≤
        (D₀ + D₁) * (2 : ℝ) ^ ((a * p) * k) := by
    have hh₀ := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right he₀ (Nat.cast_nonneg k))
    have hh₁ := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right he₁ (Nat.cast_nonneg k))
    calc
      _ ≤ D₀ * (2 : ℝ) ^ ((a * p) * k) + D₁ * (2 : ℝ) ^ ((a * p) * k) :=
        add_le_add (mul_le_mul_of_nonneg_left hh₀ hD₀) (mul_le_mul_of_nonneg_left hh₁ hD₁)
      _ = _ := by ring
  have hnonneg : 0 ≤ D₀ * (2 : ℝ) ^ ((a₀ * q₀ + b * (p - q₀)) * k) +
      D₁ * (2 : ℝ) ^ ((a₁ * q₁ + b * (p - q₁)) * k) := by positivity
  have hroot := Real.rpow_le_rpow hnonneg hcoeff (by positivity : 0 ≤ 1 / p)
  have hscale : ((D₀ + D₁) * (2 : ℝ) ^ ((a * p) * k)) ^ (1 / p) =
      (D₀ + D₁) ^ (1 / p) * (2 : ℝ) ^ (a * k) := by
    rw [Real.mul_rpow (add_nonneg hD₀ hD₁) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    field_simp
  rw [hscale] at hroot
  calc
    _ ≤ ENNReal.ofReal ((D₀ + D₁) ^ (1 / p) * (2 : ℝ) ^ (a * k)) *
        eLpNorm f (ENNReal.ofReal p) volume :=
      hb.trans (mul_le_mul (ENNReal.ofReal_le_ofReal hroot) le_rfl zero_le zero_le)
    _ = _ := by
      rw [e2_dyadicWeight_eq, ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_eq_coe_nnreal (Real.rpow_nonneg (add_nonneg hD₀ hD₁) _)]
      rfl

end PlanarNikodym
