import PlanarNikodym.Analysis.Maximal.E2DyadicInterpolation

/-! Strictly positive losses and strictly positive final frequency decay
for every exponent between the geometric and smoothing endpoints. -/
noncomputable section
namespace PlanarNikodym

theorem e2_exists_summable_interpolation_exponents
    {q₀ p q₁ : ℝ} (hq₀ : 0 < q₀) (hqp : q₀ < p) (hpq : p < q₁) :
    ∃ ε₀ ε₁ η b : ℝ, 0 < ε₀ ∧ 0 < ε₁ ∧ 0 < η ∧
      ε₀ * q₀ + b * (p - q₀) ≤ -η * p ∧
      (-1 / q₁ + ε₁) * q₁ + b * (p - q₁) ≤ -η * p := by
  have hp : 0 < p := hq₀.trans hqp
  have hq₁ : 0 < q₁ := hp.trans hpq
  let A : ℝ := (p - q₀) / (4 * q₁)
  let η : ℝ := min A (1 / 4) / p
  refine ⟨(p - q₀) / (4 * q₀ * q₁), 1 / (4 * q₁), η, -1 / (2 * q₁),
    by positivity, by positivity, ?_, ?_, ?_⟩
  · exact div_pos (lt_min (by dsimp [A]; positivity) (by norm_num)) hp
  · have he : (p - q₀) / (4 * q₀ * q₁) * q₀ + -1 / (2 * q₁) * (p - q₀) = -A := by
      dsimp [A]
      field_simp
      ring
    have hη : η * p = min A (1 / 4) := div_mul_cancel₀ _ hp.ne'
    rw [he, neg_mul, hη]
    exact neg_le_neg (min_le_left _ _)
  · have he : (-1 / q₁ + 1 / (4 * q₁)) * q₁ + -1 / (2 * q₁) * (p - q₁) =
        -(1 / 4) - p / (2 * q₁) := by
      field_simp
      ring
    have hη : η * p = min A (1 / 4) := div_mul_cancel₀ _ hp.ne'
    rw [he, neg_mul, hη]
    have hn : 0 ≤ p / (2 * q₁) := by positivity
    linarith [min_le_right A (1 / 4)]

end PlanarNikodym
