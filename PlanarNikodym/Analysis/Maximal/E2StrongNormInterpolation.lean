import PlanarNikodym.Analysis.Maximal.E2Interpolation

/-! The strong Lᵖ form of the two-finite-endpoint interpolation theorem.
Almost-everywhere input replacement is handled explicitly, which is
needed before using the actual convolution and maximal operators. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem e2_integral_power_bound_of_eLpNorm_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) {f : α → ℂ} {g : β → ℂ}
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hb : eLpNorm g (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal q) μ) :
    (∫⁻ y, ENNReal.ofReal (‖g y‖ ^ q) ∂ν) ≤
      ENNReal.ofReal (C ^ q) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q) ∂μ := by
  rw [endpoint_eLpNorm_eq_power_integral ν g hq,
    endpoint_eLpNorm_eq_power_integral μ f hq] at hb
  have hh := ENNReal.rpow_le_rpow hb hq.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hq.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC hq.le] at hh
  exact hh

theorem e2_sublinear_finite_interpolation
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : Measure β) (T : (α → ℂ) → β → ℂ)
    (hsub : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      ‖T (g + h) y‖ ≤ ‖T g y‖ + ‖T h y‖)
    (hm : ∀ g, Integrable g μ → Measurable (T g))
    (hcongr : ∀ f g, Integrable f μ → Integrable g μ → f =ᵐ[μ] g → T f =ᵐ[ν] T g)
    {p q₀ q₁ C₀ C₁ B : ℝ} (hq₀ : 0 < q₀) (hqp : q₀ < p)
    (hpq : p < q₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hB : 0 < B)
    (hlo : ∀ g, Integrable g μ → MemLp g (ENNReal.ofReal q₀) μ →
      eLpNorm (T g) (ENNReal.ofReal q₀) ν ≤
        ENNReal.ofReal C₀ * eLpNorm g (ENNReal.ofReal q₀) μ)
    (hhi : ∀ g, Integrable g μ → MemLp g (ENNReal.ofReal q₁) μ →
      eLpNorm (T g) (ENNReal.ofReal q₁) ν ≤
        ENNReal.ofReal C₁ * eLpNorm g (ENNReal.ofReal q₁) μ)
    {f : α → ℂ} (hf : Integrable f μ) (hfp : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm (T f) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal ((p * ((2 : ℝ) ^ q₀ * C₀ ^ q₀ * B ^ (p - q₀) / (p - q₀) +
        (2 : ℝ) ^ q₁ * C₁ ^ q₁ * B ^ (p - q₁) / (q₁ - p))) ^ (1 / p)) *
          eLpNorm f (ENNReal.ofReal p) μ := by
  have hp : 0 < p := hq₀.trans hqp
  have hq₁ : 0 < q₁ := hp.trans hpq
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgi : Integrable g μ := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgp : MemLp g (ENNReal.ofReal p) μ := (memLp_congr_ae hfg).mp hfp
  have hgpow : Integrable (fun x => ‖g x‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      hgp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
  have hint := e2_sublinear_finite_interpolation_integral μ ν T hsub hm hq₀ hqp hpq
    (Real.rpow_nonneg hC₀ q₀) (Real.rpow_nonneg hC₁ q₁) hB
    (fun u hu hup => e2_integral_power_bound_of_eLpNorm_bound μ ν hq₀ hC₀
      (hlo u hu ((integrable_norm_rpow_iff hu.aestronglyMeasurable
        (ENNReal.ofReal_pos.mpr hq₀).ne' ENNReal.ofReal_ne_top).mp
          (by simpa only [ENNReal.toReal_ofReal hq₀.le] using hup))))
    (fun u hu hup => e2_integral_power_bound_of_eLpNorm_bound μ ν hq₁ hC₁
      (hhi u hu ((integrable_norm_rpow_iff hu.aestronglyMeasurable
        (ENNReal.ofReal_pos.mpr hq₁).ne' ENNReal.ofReal_ne_top).mp
          (by simpa only [ENNReal.toReal_ofReal hq₁.le] using hup)))) hgi hgm hgpow
  rw [eLpNorm_congr_ae (hcongr f g hf hgi hfg), eLpNorm_congr_ae hfg,
    endpoint_eLpNorm_eq_power_integral ν (T g) hp,
    endpoint_eLpNorm_eq_power_integral μ g hp]
  have hK : 0 ≤ p * ((2 : ℝ) ^ q₀ * C₀ ^ q₀ * B ^ (p - q₀) / (p - q₀) +
      (2 : ℝ) ^ q₁ * C₁ ^ q₁ * B ^ (p - q₁) / (q₁ - p)) := by positivity
  calc
    _ ≤ (ENNReal.ofReal (p * ((2 : ℝ) ^ q₀ * C₀ ^ q₀ * B ^ (p - q₀) / (p - q₀) +
        (2 : ℝ) ^ q₁ * C₁ ^ q₁ * B ^ (p - q₁) / (q₁ - p))) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p) ∂μ) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hint (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ENNReal.ofReal_rpow_of_nonneg hK (by positivity)]

end PlanarNikodym
