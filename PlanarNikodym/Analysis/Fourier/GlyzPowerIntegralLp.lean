import PlanarNikodym.Analysis.Fourier.GlyzFiniteFamilyTransport

/-! Finite power integrals and real Lp estimates for Schwartz families.
Every conversion through ENNReal.toReal verifies finiteness first. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem glyz_schwartz_power_integral (f : SchwartzMap E ℂ) {p : ℝ≥0} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (p : ℝ))) =
      eLpNorm (f : E → ℂ) p volume ^ (p : ℝ) := by
  rw [eLpNorm_nnreal_pow_eq_lintegral hp.ne']
  congr 1
  ext x
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) p.coe_nonneg, ofReal_norm]

theorem glyz_schwartz_power_integral_ne_top (f : SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (p : ℝ))) ≠ ⊤ := by
  rw [glyz_schwartz_power_integral f hp]
  exact ENNReal.rpow_ne_top_of_nonneg p.coe_nonneg (f.memLp p volume).eLpNorm_ne_top

theorem glyz_schwartz_power_integral_toReal (f : SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (p : ℝ))).toReal =
      lpNorm (f : E → ℂ) p volume ^ (p : ℝ) := by
  rw [glyz_schwartz_power_integral f hp, ← ENNReal.toReal_rpow,
    toReal_eLpNorm (f.memLp p volume).aestronglyMeasurable]

theorem glyz_schwartz_lp_of_power_bound {ι : Type*} (I : Finset ι)
    (g : SchwartzMap E ℂ) (f : ι → SchwartzMap E ℂ)
    {p : ℝ≥0} (hp : 0 < p) {D : ℝ} (hD : 0 ≤ D)
    (h : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (p : ℝ))) ≤
      ENNReal.ofReal D * ∑ i ∈ I, ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ (p : ℝ))) :
    lpNorm (g : E → ℂ) p volume ≤
      D ^ (1 / (p : ℝ)) *
        (∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
  have hpR : (0 : ℝ) < p := hp
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.mpr fun i _ => glyz_schwartz_power_integral_ne_top (f i) hp)) h
  rw [glyz_schwartz_power_integral_toReal g hp, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hD,
    ENNReal.toReal_sum (fun i _ => glyz_schwartz_power_integral_ne_top (f i) hp)] at hh
  simp_rw [glyz_schwartz_power_integral_toReal _ hp] at hh
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg lpNorm_nonneg _) hh
    (show 0 ≤ 1 / (p : ℝ) by positivity)
  rw [← Real.rpow_mul lpNorm_nonneg,
    show (p : ℝ) * (1 / (p : ℝ)) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow hD (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg lpNorm_nonneg _)] at hroot
  exact hroot

end PlanarNikodym
