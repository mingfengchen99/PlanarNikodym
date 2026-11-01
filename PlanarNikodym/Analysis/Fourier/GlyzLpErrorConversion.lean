import PlanarNikodym.Analysis.Fourier.GlyzPowerIntegralLp
import PlanarNikodym.Analysis.Fourier.CompactInputL2Error

/-! Exact conversion from the proved power-integral estimates to
finite real Lp norms, with an additive error. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PlanarNikodym

theorem glyz_lp_of_power_error_bound {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (g : X → ℂ) (f : ι → X → ℂ)
    {p : ℝ≥0} (hp : 1 ≤ p) (hg : MemLp g p μ) (hf : ∀ i ∈ I, MemLp (f i) p μ)
    {D e : ℝ} (hD : 0 ≤ D) (he : 0 ≤ e)
    (h : (∫⁻ x, ‖g x‖ₑ ^ (p : ℝ) ∂μ) ≤
      ENNReal.ofReal D * ∑ i ∈ I, ∫⁻ x, ‖f i x‖ₑ ^ (p : ℝ) ∂μ +
        ENNReal.ofReal e ^ (p : ℝ)) :
    lpNorm g p μ ≤ D ^ (1 / (p : ℝ)) *
      (∑ i ∈ I, lpNorm (f i) p μ ^ (p : ℝ)) ^ (1 / (p : ℝ)) + e := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have heq (F : X → ℂ) : (∫⁻ x, ‖F x‖ₑ ^ (p : ℝ) ∂μ) = eLpNorm F p μ ^ (p : ℝ) :=
    (eLpNorm_nnreal_pow_eq_lintegral hpne).symm
  simp_rw [heq] at h
  have hfin : (∑ i ∈ I, eLpNorm (f i) p μ ^ (p : ℝ)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i hi =>
      ENNReal.rpow_ne_top_of_nonneg p.coe_nonneg (hf i hi).eLpNorm_ne_top
  have hR : ENNReal.ofReal D * (∑ i ∈ I, eLpNorm (f i) p μ ^ (p : ℝ)) +
      ENNReal.ofReal e ^ (p : ℝ) ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin,
      ENNReal.rpow_ne_top_of_nonneg p.coe_nonneg ENNReal.ofReal_ne_top⟩
  have hh := ENNReal.toReal_mono hR h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
      (ENNReal.rpow_ne_top_of_nonneg p.coe_nonneg ENNReal.ofReal_ne_top), ENNReal.toReal_mul, ENNReal.toReal_ofReal hD,
    ENNReal.toReal_sum (fun i hi =>
      ENNReal.rpow_ne_top_of_nonneg p.coe_nonneg (hf i hi).eLpNorm_ne_top),
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    toReal_eLpNorm hg.aestronglyMeasurable, ENNReal.toReal_ofReal he] at hh
  have hterm (i : ι) (hi : i ∈ I) :
      (eLpNorm (f i) p μ ^ (p : ℝ)).toReal = lpNorm (f i) p μ ^ (p : ℝ) := by
    rw [← ENNReal.toReal_rpow, toReal_eLpNorm (hf i hi).aestronglyMeasurable]
  rw [Finset.sum_congr rfl hterm] at hh
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg lpNorm_nonneg _) hh
    (show 0 ≤ 1 / (p : ℝ) by positivity)
  rw [← Real.rpow_mul lpNorm_nonneg,
    show (p : ℝ) * (1 / (p : ℝ)) = 1 by field_simp, Real.rpow_one] at hroot
  apply hroot.trans
  have hs : 0 ≤ ∑ i ∈ I, lpNorm (f i) p μ ^ (p : ℝ) :=
    Finset.sum_nonneg fun i hi => Real.rpow_nonneg lpNorm_nonneg _
  have hsub := Real.rpow_add_le_add_rpow (mul_nonneg hD hs) (Real.rpow_nonneg he (p : ℝ))
    (show 0 ≤ 1 / (p : ℝ) by positivity) ((div_le_one hp0).mpr hp)
  rw [Real.mul_rpow hD hs, ← Real.rpow_mul he,
    show (p : ℝ) * (1 / (p : ℝ)) = 1 by field_simp, Real.rpow_one] at hsub
  exact hsub

end PlanarNikodym
