import Mathlib.Analysis.Fourier.LpSpace

/-! Compatibility of the actual Fourier integral with the Hilbert space
Fourier transform for integrable square-integrable functions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The continuous Fourier integral is the representative of the abstract
L² Fourier transform whenever the original function belongs to L¹ and L².
The proof compares actual integrals against compactly supported smooth
tests, rather than assuming simultaneous L¹/L² approximation. -/
theorem fourierIntegral_ae_eq_L2 {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure E)) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  intro g hg hc
  let test : SchwartzMap E ℂ :=
    (hc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have hd := congrArg (fun T : TemperedDistribution E ℂ => T test)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  have hp : (∫ x, 𝓕 f x * test x) = ∫ x, f x * 𝓕 (⇑test) x := by
    have hflip : (innerₗ E).flip = innerₗ E := by ext x y; exact real_inner_comm x y
    simpa only [Real.fourier_eq, Real.fourierInv_eq, VectorFourier.fourierIntegral,
      smul_eq_mul, hflip, innerₗ_apply_apply, LinearMap.neg_apply, neg_neg] using
      (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (μ := volume) (ν := volume) (L := innerₗ E) Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ h1 test.integrable)
  calc
    _ = ∫ x, 𝓕 f x * test x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [test, Complex.real_smul, mul_comm]
    _ = ∫ x, f x * 𝓕 (⇑test) x := hp
    _ = ∫ x, 𝓕 test x • (h2.toLp f : Lp ℂ 2 (volume : Measure E)) x := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx]
      simp only [SchwartzMap.fourier_coe, smul_eq_mul, mul_comm]
    _ = ∫ x, test x • (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure E)) x := hd
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [test, Complex.real_smul]

/-- The actual Fourier integral of an L¹∩L² input is square integrable. -/
theorem memLp_fourierIntegral_two {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourierIntegral_ae_eq_L2 h1 h2)).2 (Lp.memLp _)

/-- Plancherel for the actual Fourier integral, with no smoothness
assumption on the L¹∩L² input. -/
theorem eLpNorm_fourierIntegral_two {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  calc
    _ = eLpNorm (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure E)) 2 volume :=
      eLpNorm_congr_ae (fourierIntegral_ae_eq_L2 h1 h2)
    _ = ‖𝓕 (h2.toLp f)‖ₑ := (Lp.enorm_def (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure E))).symm
    _ = ‖h2.toLp f‖ₑ := by rw [← ofReal_norm, Lp.norm_fourier_eq, ofReal_norm]
    _ = _ := Lp.enorm_toLp h2

/-- Exact squared mass of the actual Fourier integral for L¹∩L² data. -/
theorem lintegral_fourierIntegral_sq {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫⁻ ξ : E, ‖𝓕 f ξ‖ₑ ^ (2 : ℕ)) = ∫⁻ x : E, ‖f x‖ₑ ^ (2 : ℕ) := by
  have he := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) (eLpNorm_fourierIntegral_two h1 h2)
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)), ENNReal.toReal_ofNat,
    ← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one] at he
  simpa only [ENNReal.rpow_two] using he

/-- The inverse integral also represents the Hilbert space inverse on
every L¹∩L² input. -/
theorem fourierInvIntegral_ae_eq_L2 {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    𝓕⁻ f =ᵐ[volume] (𝓕⁻ (h2.toLp f) : Lp ℂ 2 (volume : Measure E)) := by
  have hcont : Continuous (𝓕⁻ f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (show Continuous (fun p : E × E => (-innerₗ E) p.1 p.2) from
        (innerSL ℝ).continuous₂.neg) h1
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  intro g hg hc
  let test : SchwartzMap E ℂ :=
    (hc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have hd := congrArg (fun T : TemperedDistribution E ℂ => T test)
    (Lp.fourierInv_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at hd
  have hp : (∫ x, 𝓕⁻ f x * test x) = ∫ x, f x * 𝓕⁻ (⇑test) x := by
    have hflip : (-innerₗ E).flip = -innerₗ E := by
      ext x y
      change -inner ℝ y x = -inner ℝ x y
      rw [real_inner_comm]
    simpa only [Real.fourier_eq, Real.fourierInv_eq, VectorFourier.fourierIntegral,
      smul_eq_mul, hflip, innerₗ_apply_apply, LinearMap.neg_apply, neg_neg] using
      (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (μ := volume) (ν := volume) (L := -innerₗ E) Real.continuous_fourierChar
        (innerSL ℝ).continuous₂.neg h1 test.integrable)
  calc
    _ = ∫ x, 𝓕⁻ f x * test x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [test, Complex.real_smul, mul_comm]
    _ = ∫ x, f x * 𝓕⁻ (⇑test) x := hp
    _ = ∫ x, 𝓕⁻ test x • (h2.toLp f : Lp ℂ 2 (volume : Measure E)) x := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx]
      simp only [SchwartzMap.fourierInv_coe, smul_eq_mul, mul_comm]
    _ = ∫ x, test x • (𝓕⁻ (h2.toLp f) : Lp ℂ 2 (volume : Measure E)) x := hd
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [test, Complex.real_smul]

theorem memLp_fourierInvIntegral_two {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) : MemLp (𝓕⁻ f) 2 :=
  (memLp_congr_ae (fourierInvIntegral_ae_eq_L2 h1 h2)).2 (Lp.memLp _)

theorem eLpNorm_fourierInvIntegral_two {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    eLpNorm (𝓕⁻ f) 2 volume = eLpNorm f 2 volume := by
  calc
    _ = eLpNorm (𝓕⁻ (h2.toLp f) : Lp ℂ 2 (volume : Measure E)) 2 volume :=
      eLpNorm_congr_ae (fourierInvIntegral_ae_eq_L2 h1 h2)
    _ = ‖𝓕⁻ (h2.toLp f)‖ₑ := (Lp.enorm_def (𝓕⁻ (h2.toLp f) : Lp ℂ 2 (volume : Measure E))).symm
    _ = ‖h2.toLp f‖ₑ := by
      change ‖(Lp.fourierTransformₗᵢ E ℂ).symm (h2.toLp f)‖ₑ = _
      rw [← ofReal_norm, (Lp.fourierTransformₗᵢ E ℂ).symm.norm_map, ofReal_norm]
    _ = _ := Lp.enorm_toLp h2

theorem lintegral_fourierInvIntegral_sq {f : E → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫⁻ ξ : E, ‖𝓕⁻ f ξ‖ₑ ^ (2 : ℕ)) = ∫⁻ x : E, ‖f x‖ₑ ^ (2 : ℕ) := by
  have he := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ))
    (eLpNorm_fourierInvIntegral_two h1 h2)
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞)), ENNReal.toReal_ofNat,
    ← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one] at he
  simpa only [ENNReal.rpow_two] using he

end PlanarNikodym
