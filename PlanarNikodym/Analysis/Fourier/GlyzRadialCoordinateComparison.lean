import PlanarNikodym.Analysis.Fourier.GlyzCoordinateWeight
import PlanarNikodym.Analysis.Fourier.GlyzAffineCutoff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Uniform conversion of the radial local-decoupling weight to the
actual coordinate measure used by the transverse convolution argument.
The two inverse radii may differ by a fixed factor, as occurs with
rounded dyadic depths. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem glyzNormWeight_le_scaled_coordinate (l A : ℕ) {L b c : ℝ}
    (hL : 1 ≤ L) (hb : 0 < b) (hc : 0 < c) (hbc : b ≤ L * c)
    (y : GlyzSpace l) :
    glyzNormWeight A (c • y) ≤
      L ^ A * glyzDecayWeight A (b • ((EuclideanSpace.equiv (Fin l) ℝ) y)) := by
  have hy : ‖(EuclideanSpace.equiv (Fin l) ℝ) y‖ ≤ ‖y‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i => PiLp.norm_apply_le y i
  have hn : ‖b • ((EuclideanSpace.equiv (Fin l) ℝ) y)‖ ≤ L * ‖c • y‖ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hb, abs_of_pos hc]
    nlinarith [mul_le_mul_of_nonneg_left hy hb.le,
      mul_le_mul_of_nonneg_right hbc (norm_nonneg y)]
  have hmax : max 1 ‖b • ((EuclideanSpace.equiv (Fin l) ℝ) y)‖ ≤
      L * max 1 ‖c • y‖ := by
    apply max_le
    · nlinarith [le_max_left (1 : ℝ) ‖c • y‖]
    · exact hn.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))
  have hpow := pow_le_pow_left₀
    (show 0 ≤ max (1 : ℝ) ‖b • ((EuclideanSpace.equiv (Fin l) ℝ) y)‖ by positivity)
    hmax A
  rw [mul_pow] at hpow
  unfold glyzNormWeight glyzDecayWeight
  have hd : 1 / (max (1 : ℝ) ‖c • y‖) ^ A ≤
      L ^ A / (max (1 : ℝ) ‖b • ((EuclideanSpace.equiv (Fin l) ℝ) y)‖) ^ A :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpow)
  simpa only [div_eq_mul_inv, one_mul] using hd

theorem glyz_inv_volume_closedBall (l : ℕ) {b : ℝ} (hb : 0 < b) :
    (volume (closedBall (0 : GlyzSpace l) b⁻¹))⁻¹ =
      ENNReal.ofReal (b ^ l) * (volume (closedBall (0 : GlyzSpace l) 1))⁻¹ := by
  rw [Measure.addHaar_closedBall' volume (0 : GlyzSpace l) (inv_nonneg.mpr hb.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, inv_pow,
    ENNReal.ofReal_inv_of_pos (pow_pos hb l)]
  rw [ENNReal.mul_inv (Or.inr measure_closedBall_lt_top.ne)
    (Or.inr (measure_closedBall_pos volume (0 : GlyzSpace l) zero_lt_one).ne'),
    inv_inv]

/-- The fixed comparison constant is chosen before both radii and the
physical point. No integrability hypothesis on the tested function is
needed for this pointwise density comparison. -/
theorem exists_uniform_glyz_radial_coordinate_comparison (l A : ℕ)
    {L : ℝ} (hL : 1 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b c : ℝ), 0 < b → 0 < c → b ≤ L * c →
      ∀ y : GlyzSpace l,
      (volume (closedBall (0 : GlyzSpace l) b⁻¹))⁻¹ *
          ENNReal.ofReal (glyzNormWeight A (c • y)) ≤
        ENNReal.ofReal K *
          ENNReal.ofReal (glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) y)) := by
  let v := volume (closedBall (0 : GlyzSpace l) 1)
  have hv0 : v ≠ 0 := (measure_closedBall_pos volume (0 : GlyzSpace l) zero_lt_one).ne'
  have hvt : v ≠ ⊤ := measure_closedBall_lt_top.ne
  have hv : 0 < v.toReal := ENNReal.toReal_pos hv0 hvt
  refine ⟨v.toReal⁻¹ * L ^ A, mul_pos (inv_pos.mpr hv) (pow_pos (by linarith) A), ?_⟩
  intro b c hb hc hbc y
  have he : v⁻¹ = ENNReal.ofReal v.toReal⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hv, ENNReal.ofReal_toReal hvt]
  rw [glyz_inv_volume_closedBall l hb]
  change (ENNReal.ofReal (b ^ l) * v⁻¹) * _ ≤ _
  rw [he]
  have h := ENNReal.ofReal_le_ofReal
    (glyzNormWeight_le_scaled_coordinate l A hL hb hc hbc y)
  apply (mul_le_mul' le_rfl h).trans_eq
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ A),
    ENNReal.ofReal_mul (inv_nonneg.mpr hv.le)]
  unfold glyzIsotropicWeight
  rw [ENNReal.ofReal_mul (pow_nonneg hb.le l)]
  ring

end PlanarNikodym
