import PlanarNikodym.Analysis.Fourier.GlyzContinuousGlobalization
import PlanarNikodym.Analysis.Fourier.GlyzNormWeightMass

/-! The continuous-center bound for the actual decoupling weight.
The ball radius cancels exactly from its main coefficient. -/
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal BigOperators
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_normWeight_mass_ball_ratio (A : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ x : E, ENNReal.ofReal (glyzNormWeight A (ρ⁻¹ • x))) /
      volume (closedBall (0 : E) ρ) =
    (∫⁻ x : E, ENNReal.ofReal (glyzNormWeight A x)) /
      volume (closedBall (0 : E) 1) := by
  have hm := glyz_lintegral_normWeight_smul_sub (E := E) A (inv_pos.mpr hρ) 0
  simp only [sub_zero, inv_pow, inv_inv] at hm
  rw [hm, addHaar_closedBall' volume (0 : E) hρ.le]
  exact ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hρ _))
    ENNReal.ofReal_ne_top

/-- A finite positive constant independent of every physical radius,
all pieces and all local error parameters. -/
theorem exists_glyz_normWeight_globalization_constant {A : ℕ}
    (hA : Module.finrank ℝ E < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (I : Finset ι)
      (F : E → ℝ≥0∞) (G : ι → E → ℝ≥0∞),
      Measurable F → (∀ i ∈ I, Measurable (G i)) → ∀ L ρ : ℝ, 0 < ρ →
      Function.support F ⊆ closedBall (0 : E) L → ∀ D e : ℝ≥0∞,
      (∀ a ∈ closedBall (0 : E) (L + ρ),
        (∫⁻ x in closedBall a ρ, F x) ≤
          D * ∑ i ∈ I, (∫⁻ x, G i x *
            ENNReal.ofReal (glyzNormWeight A (ρ⁻¹ • (x - a)))) + e) →
      (∫⁻ x, F x) ≤ ENNReal.ofReal C * D * ∑ i ∈ I, (∫⁻ x, G i x) +
        e * (volume (closedBall (0 : E) (L + ρ)) / volume (closedBall (0 : E) ρ)) := by
  let c := (∫⁻ x : E, ENNReal.ofReal (glyzNormWeight A x)) /
    volume (closedBall (0 : E) 1)
  have hb0 : volume (closedBall (0 : E) 1) ≠ 0 := (measure_closedBall_pos volume 0 zero_lt_one).ne'
  have hbT : volume (closedBall (0 : E) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hc0 : c ≠ 0 := (ENNReal.div_pos (glyzNormWeight_lintegral_pos A).ne' hbT).ne'
  have hcT : c ≠ ⊤ := ENNReal.div_ne_top (glyzNormWeight_lintegral_ne_top hA) hb0
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hcT, fun I F G hF hG L ρ hρ hs D e hlocal => ?_⟩
  have h := glyz_continuous_center_globalization volume I F G
    (fun x => ENNReal.ofReal (glyzNormWeight A (ρ⁻¹ • x))) hF hG
    (ENNReal.measurable_ofReal.comp
      ((continuous_glyzNormWeight A).comp (continuous_const.smul continuous_id)).measurable)
    L hρ hs D e hlocal
  rw [glyz_normWeight_mass_ball_ratio A hρ] at h
  change (∫⁻ x, F x) ≤ D * c * ∑ i ∈ I, (∫⁻ x, G i x) +
    e * (volume (closedBall (0 : E) (L + ρ)) / volume (closedBall (0 : E) ρ)) at h
  simpa only [ENNReal.ofReal_toReal hcT, mul_comm D c] using h

end PlanarNikodym
