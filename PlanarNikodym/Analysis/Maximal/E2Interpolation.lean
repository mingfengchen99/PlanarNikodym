import PlanarNikodym.Analysis.Maximal.E2Layercake

/-! Real-variable interpolation for a genuinely sublinear operator and
two finite strong endpoints. The free truncation parameter is retained;
choosing it as a dyadic power gives the decay needed in §2.5. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem e2_sublinear_finite_interpolation_integral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : Measure β) (T : (α → ℂ) → β → ℂ)
    (hsub : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      ‖T (g + h) y‖ ≤ ‖T g y‖ + ‖T h y‖)
    (hm : ∀ g, Integrable g μ → Measurable (T g))
    {p q₀ q₁ A₀ A₁ B : ℝ} (hq₀ : 0 < q₀) (hqp : q₀ < p)
    (hpq : p < q₁) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hB : 0 < B)
    (hlo : ∀ g, Integrable g μ → Integrable (fun x => ‖g x‖ ^ q₀) μ →
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ q₀) ∂ν) ≤
        ENNReal.ofReal A₀ * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q₀) ∂μ)
    (hhi : ∀ g, Integrable g μ → Integrable (fun x => ‖g x‖ ^ q₁) μ →
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ q₁) ∂ν) ≤
        ENNReal.ofReal A₁ * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q₁) ∂μ)
    {f : α → ℂ} (hf : Integrable f μ) (hfm : Measurable f)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) μ) :
    (∫⁻ y, ENNReal.ofReal (‖T f y‖ ^ p) ∂ν) ≤
      ENNReal.ofReal (p * ((2 : ℝ) ^ q₀ * A₀ * B ^ (p - q₀) / (p - q₀) +
        (2 : ℝ) ^ q₁ * A₁ * B ^ (p - q₁) / (q₁ - p))) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p) ∂μ := by
  classical
  have hp0 : 0 < p := hq₀.trans hqp
  let J₀ : ℝ → ℝ≥0∞ := fun t => ∫⁻ x,
    ({x | t ≤ B * ‖f x‖}.indicator (fun x => ENNReal.ofReal (‖f x‖ ^ q₀))) x ∂μ
  let J₁ : ℝ → ℝ≥0∞ := fun t => ∫⁻ x,
    ({x | B * ‖f x‖ < t}.indicator (fun x => ENNReal.ofReal (‖f x‖ ^ q₁))) x ∂μ
  have hJ₀ : Measurable J₀ := by
    have hh : Measurable (fun z : ℝ × α =>
        {z : ℝ × α | z.1 ≤ B * ‖f z.2‖}.indicator
          (fun z => ENNReal.ofReal (‖f z.2‖ ^ q₀)) z) := by
      exact (((hfm.comp measurable_snd).norm.pow_const _).ennreal_ofReal).indicator
        (measurableSet_le measurable_fst (measurable_const.mul (hfm.comp measurable_snd).norm))
    exact hh.lintegral_prod_right'
  have hJ₁ : Measurable J₁ := by
    have hh : Measurable (fun z : ℝ × α =>
        {z : ℝ × α | B * ‖f z.2‖ < z.1}.indicator
          (fun z => ENNReal.ofReal (‖f z.2‖ ^ q₁)) z) := by
      exact (((hfm.comp measurable_snd).norm.pow_const _).ennreal_ofReal).indicator
        (measurableSet_lt (measurable_const.mul (hfm.comp measurable_snd).norm) measurable_fst)
    exact hh.lintegral_prod_right'
  have hweight (q A : ℝ) (hA : 0 ≤ A) (J : ℝ → ℝ≥0∞)
      (t : ℝ) (ht : 0 < t) :
      (ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) * J t) * ENNReal.ofReal (t ^ (p - 1)) =
        ENNReal.ofReal ((2 : ℝ) ^ q * A) * (ENNReal.ofReal (t ^ (p - q - 1)) * J t) := by
    have he : ((2 : ℝ) ^ q * A / t ^ q) * t ^ (p - 1) =
        (2 : ℝ) ^ q * A * t ^ (p - q - 1) := by
      have hpw : t ^ (p - q - 1) = t ^ (p - 1) / t ^ q := by
        rw [← Real.rpow_sub ht]; congr 1; ring
      rw [hpw]
      ring
    calc
      _ = (ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) *
          ENNReal.ofReal (t ^ (p - 1))) * J t := by ac_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), he,
          ENNReal.ofReal_mul (by positivity)]
        ac_rfl
  rw [lintegral_rpow_eq_lintegral_meas_le_mul ν
    (Filter.Eventually.of_forall (fun y => norm_nonneg (T f y)))
    (hm f hf).norm.aemeasurable (hq₀.trans hqp)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        (ENNReal.ofReal ((2 : ℝ) ^ q₀ * A₀ / t ^ q₀) * J₀ t +
          ENNReal.ofReal ((2 : ℝ) ^ q₁ * A₁ / t ^ q₁) * J₁ t) *
            ENNReal.ofReal (t ^ (p - 1)) := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_le_mul_left
        (e2_sublinear_two_endpoint_tail μ ν T hsub hm hq₀ hqp hpq hA₀ hA₁ hB
          hlo hhi hf hfm hfp ht) _
    _ = ENNReal.ofReal p *
        (ENNReal.ofReal ((2 : ℝ) ^ q₀ * A₀) *
          (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q₀ - 1)) * J₀ t) +
        ENNReal.ofReal ((2 : ℝ) ^ q₁ * A₁) *
          (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q₁ - 1)) * J₁ t)) := by
      congr 1
      calc
        _ = ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal ((2 : ℝ) ^ q₀ * A₀) *
              (ENNReal.ofReal (t ^ (p - q₀ - 1)) * J₀ t) +
            ENNReal.ofReal ((2 : ℝ) ^ q₁ * A₁) *
              (ENNReal.ofReal (t ^ (p - q₁ - 1)) * J₁ t) := by
          apply lintegral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          rw [add_mul, hweight q₀ A₀ hA₀ J₀ t ht, hweight q₁ A₁ hA₁ J₁ t ht]
        _ = _ := by
          have hfirst : Measurable (fun t : ℝ => ENNReal.ofReal ((2 : ℝ) ^ q₀ * A₀) *
              (ENNReal.ofReal (t ^ (p - q₀ - 1)) * J₀ t)) :=
            measurable_const.mul ((measurable_id.pow_const _).ennreal_ofReal.mul hJ₀)
          rw [lintegral_add_left hfirst,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
      rw [glyz_truncated_power_layercake μ hfm.norm (fun x => norm_nonneg (f x)) hq₀ hqp hB,
        e2_low_truncated_power_layercake μ hfm.norm (fun x => norm_nonneg (f x))
          (hq₀.trans hqp) hpq hB]
      rw [← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end PlanarNikodym
