import PlanarNikodym.Geometry.AnalyticCoefficientBounds

/-! A genuinely convergent Banach-valued series for the rescaled vertical
coefficients of an arbitrary joint real analytic power series. -/
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticCoefficientTerm_uniform_bound
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (R C : ℝ)
    (hR : 0 < R) (_hC : 0 ≤ C) (hb : ∀ n, ‖p n‖ ≤ C / R ^ n) (k n : ℕ) :
    ‖analyticCoefficientTerm p (R / 2) k n‖ ≤ C * (2 / R) ^ k := by
  calc
    _ ≤ (2 : ℝ) ^ (n + k) * ‖p (n + k)‖ * (R / 2) ^ n :=
      norm_analyticCoefficientTerm_le p (by positivity) k n
    _ ≤ (2 : ℝ) ^ (n + k) * (C / R ^ (n + k)) * (R / 2) ^ n := by
      gcongr
      exact hb (n + k)
    _ = _ := by
      rw [pow_add, pow_add, div_pow, div_pow]
      field_simp

def analyticCoefficientSeries
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hb : ∀ n, ‖p n‖ ≤ C / R ^ n) :
    FormalMultilinearSeries ℝ E (lp (fun _ : ℕ => ℝ) ∞) := fun k =>
  boundedSequenceMultilinear (analyticCoefficientTerm p (R / 2) k)
    (C * (2 / R) ^ k) (by positivity)
    (analyticCoefficientTerm_uniform_bound p R C hR hC hb k)

@[simp] theorem analyticCoefficientSeries_apply
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hb : ∀ n, ‖p n‖ ≤ C / R ^ n)
    (k n : ℕ) (v : Fin k → E) :
    analyticCoefficientSeries p R C hR hC hb k v n =
      p.changeOriginSeries n k (fun i => (v i, 0)) (fun _ => (0, R / 2)) := rfl

theorem analyticCoefficientSeries_radius_pos
    (p : FormalMultilinearSeries ℝ (E × ℝ) ℝ) (R C : ℝ)
    (hR : 0 < R) (hC : 0 ≤ C) (hb : ∀ n, ‖p n‖ ≤ C / R ^ n) :
    0 < (analyticCoefficientSeries p R C hR hC hb).radius := by
  let r : ℝ≥0 := ⟨R / 2, by positivity⟩
  have hr : (r : ℝ≥0∞) ≤ (analyticCoefficientSeries p R C hR hC hb).radius := by
    apply (analyticCoefficientSeries p R C hR hC hb).le_radius_of_bound C
    intro k
    calc
      _ ≤ (C * (2 / R) ^ k) * (r : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right
          (norm_boundedSequenceMultilinear_le _ _ _ _) (by positivity)
      _ = C := by
        change (C * (2 / R) ^ k) * (R / 2) ^ k = C
        rw [mul_assoc, ← mul_pow]
        have he : 2 / R * (R / 2) = (1 : ℝ) := by field_simp
        rw [he, one_pow, mul_one]
  exact (show (0 : ℝ≥0∞) < r by exact_mod_cast (show (0 : ℝ) < R / 2 by positivity)).trans_le hr

end PlanarNikodym
