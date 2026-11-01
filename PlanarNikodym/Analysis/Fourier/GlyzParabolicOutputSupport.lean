import PlanarNikodym.Analysis.Fourier.GlyzParabolicRescaling
import PlanarNikodym.Analysis.Fourier.GlyzMomentConeCoordinates

/-! Polynomial output-domain growth of the actual compact parabolic
extension. Compactness is used before choosing frequency, center, scale
or input; no support certificate for the resulting operator is assumed. -/
noncomputable section
open Set Metric MeasureTheory
namespace PlanarNikodym

theorem norm_lowerDegreeDilation_le (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x : Aux (n + 1)) :
    ‖lowerDegreeDilation n δ hδ.ne' x‖ ≤ (δ ^ n)⁻¹ * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [lowerDegreeDilation_apply, norm_mul, Real.norm_eq_abs,
    abs_of_pos (div_pos (pow_pos hδ _) (pow_pos hδ _))]
  have hi : δ ^ (i : ℕ) / δ ^ n ≤ (δ ^ n)⁻¹ := by
    simpa only [one_div] using
      div_le_div_of_nonneg_right (pow_le_one₀ hδ.le hδ1) (pow_nonneg hδ.le n)
  exact mul_le_mul hi (norm_le_pi_norm x i) (norm_nonneg _) (by positivity)

/-- Output support in coefficient coordinates grows by at most δ⁻ⁿ. -/
theorem exists_glyz_compact_parabolic_output_bound {d n : ℕ}
    (A : GlyzParabolicSymbolVariables d n → ℂ) (hA : HasCompactSupport A) :
    ∃ L : ℝ, 0 < L ∧ ∀ (H : GlyzParabolicSymbolVariables d n → ℝ)
      (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (α R : ℝ) (g : Plane → ℂ),
      Function.support (polynomialExtension
        (glyzCompactParabolicAmplitude A H q δ hδ.ne' α) g R) ⊆
          closedBall (0 : Aux (n + 1)) ((δ ^ n)⁻¹ * L) := by
  obtain ⟨L, hL, hb⟩ := hA.isCompact.isBounded.exists_pos_norm_le
  refine ⟨L, hL, fun H q δ hδ hδ1 α R g w hw => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  by_contra hn
  have hzero (τ η : ℝ) : glyzCompactParabolicAmplitude A H q δ hδ.ne' α w τ η = 0 := by
    let z : GlyzParabolicSymbolVariables d n :=
      (((q, (lowerDegreeDilation n δ hδ.ne').symm w), (τ, η)), δ)
    have ha : A z = 0 := by
      by_contra hne
      have hz := hb z (subset_tsupport _ hne)
      have hy : ‖(lowerDegreeDilation n δ hδ.ne').symm w‖ ≤ L :=
        (norm_snd_le _).trans ((norm_fst_le _).trans ((norm_fst_le _).trans hz))
      have hh := (norm_lowerDegreeDilation_le n hδ hδ1
        ((lowerDegreeDilation n δ hδ.ne').symm w)).trans
        (mul_le_mul_of_nonneg_left hy (by positivity))
      exact hn (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh)
    change A z * _ = 0
    rw [ha, zero_mul]
  apply hw
  unfold polynomialExtension
  simp only [hzero, mul_zero, zero_mul, integral_zero]

/-- The same bound in any fixed Euclidean coordinates. -/
theorem exists_glyz_compact_parabolic_cone_output_bound {d n : ℕ}
    (A : GlyzParabolicSymbolVariables d n → ℂ) (hA : HasCompactSupport A)
    (T : GlyzConeSpace n ≃L[ℝ] Aux (n + 1)) :
    ∃ L : ℝ, 0 < L ∧ ∀ (H : GlyzParabolicSymbolVariables d n → ℝ)
      (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (α R : ℝ) (g : Plane → ℂ),
      Function.support (fun x => polynomialExtension
        (glyzCompactParabolicAmplitude A H q δ hδ.ne' α) g R (T x)) ⊆
          closedBall (0 : GlyzConeSpace n) ((δ ^ n)⁻¹ * L) := by
  obtain ⟨L, hL, hb⟩ := exists_glyz_compact_parabolic_output_bound A hA
  refine ⟨(‖T.symm.toContinuousLinearMap‖ + 1) * L, by positivity,
    fun H q δ hδ hδ1 α R g x hx => ?_⟩
  have ht := hb H q δ hδ hδ1 α R g hx
  rw [mem_closedBall, dist_zero_right] at ht ⊢
  have hn : ‖x‖ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
      using T.symm.toContinuousLinearMap.le_opNorm (T x)
  have h := hn.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
  nlinarith [inv_nonneg.mpr (pow_nonneg hδ.le n), norm_nonneg T.symm.toContinuousLinearMap]

/-- The center-volume factor from globalization is only a fixed
polynomial in the inverse time scale. -/
theorem glyz_parabolic_output_ball_ratio {n : ℕ} {L δ : ℝ}
    (hL : 0 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    volume (closedBall (0 : GlyzConeSpace n) ((δ ^ n)⁻¹ * L + 1)) /
      volume (closedBall (0 : GlyzConeSpace n) 1) ≤
        ENNReal.ofReal ((L + 1) ^ Module.finrank ℝ (GlyzConeSpace n) *
          ((δ ^ n)⁻¹) ^ Module.finrank ℝ (GlyzConeSpace n)) := by
  have hR : 0 ≤ (δ ^ n)⁻¹ * L + 1 := by positivity
  have hb0 : volume (closedBall (0 : GlyzConeSpace n) 1) ≠ 0 :=
    (measure_closedBall_pos volume 0 zero_lt_one).ne'
  have hbT : volume (closedBall (0 : GlyzConeSpace n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [MeasureTheory.Measure.addHaar_closedBall' volume (0 : GlyzConeSpace n) hR,
    ENNReal.mul_div_cancel_right hb0 hbT]
  apply ENNReal.ofReal_le_ofReal
  have hi : 1 ≤ (δ ^ n)⁻¹ := (one_le_inv₀ (pow_pos hδ n)).mpr (pow_le_one₀ hδ.le hδ1)
  have hbound : (δ ^ n)⁻¹ * L + 1 ≤ (L + 1) * (δ ^ n)⁻¹ := by nlinarith
  simpa only [mul_pow] using pow_le_pow_left₀ hR hbound (Module.finrank ℝ (GlyzConeSpace n))

end PlanarNikodym
