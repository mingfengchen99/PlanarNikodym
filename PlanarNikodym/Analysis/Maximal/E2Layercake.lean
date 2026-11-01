import PlanarNikodym.Analysis.Maximal.E2Truncation

/-! Tonelli's second, low-amplitude term for interpolation between two
finite exponents. The high-amplitude term is `glyz_truncated_power_layercake`.
Both identities retain the truncation scale, needed for frequency decay. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem e2_lintegral_power_tail {p q a : ℝ} (hpq : p < q) (ha : 0 < a) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (p - q - 1))) =
      ENNReal.ofReal (a ^ (p - q) / (q - p)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (p - q - 1)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] (fun t : ℝ => t ^ (p - q - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (ha.trans ht).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_Ioi_rpow_of_lt (by linarith) ha]
  have he : p - q - 1 + 1 = p - q := by ring
  rw [he]
  congr 1
  rw [show q - p = -(p - q) by ring, div_neg]
  ring

theorem e2_low_truncated_power_layercake
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {F : α → ℝ} (hF : Measurable F) (hFn : ∀ x, 0 ≤ F x)
    {p q B : ℝ} (hp : 0 < p) (hpq : p < q) (hB : 0 < B) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q - 1)) *
      ∫⁻ x, ({x | B * F x < t}.indicator (fun x => ENNReal.ofReal ((F x) ^ q))) x ∂μ) =
      ENNReal.ofReal (B ^ (p - q) / (q - p)) *
        ∫⁻ x, ENNReal.ofReal ((F x) ^ p) ∂μ := by
  classical
  let H : ℝ → α → ℝ≥0∞ := fun t x =>
    {z : ℝ × α | B * F z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (z.1 ^ (p - q - 1)) * ENNReal.ofReal ((F z.2) ^ q)) (t, x)
  have hHm : Measurable (Function.uncurry H) := by
    apply Measurable.indicator
    · exact (measurable_fst.pow_const _).ennreal_ofReal.mul
        ((hF.comp measurable_snd).pow_const q).ennreal_ofReal
    · exact measurableSet_lt (measurable_const.mul (hF.comp measurable_snd)) measurable_fst
  have he (t : ℝ) : ENNReal.ofReal (t ^ (p - q - 1)) *
      (∫⁻ x, ({x | B * F x < t}.indicator (fun x => ENNReal.ofReal ((F x) ^ q))) x ∂μ) =
      ∫⁻ x, H t x ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    by_cases hx : B * F x < t <;> simp [H, hx]
  simp_rw [he]
  rw [lintegral_lintegral_swap hHm.aemeasurable]
  have hinner (x : α) : (∫⁻ t in Ioi (0 : ℝ), H t x) =
      ENNReal.ofReal (B ^ (p - q) / (q - p)) * ENNReal.ofReal ((F x) ^ p) := by
    by_cases hx : F x = 0
    · have hz : (fun t => H t x) = 0 := by
        funext t
        simp only [H, Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs <;> simp [hx, Real.zero_rpow (hp.trans hpq).ne']
      rw [hz]
      change (∫⁻ t in Ioi (0 : ℝ), (0 : ℝ≥0∞)) = _
      simp [hx, Real.zero_rpow hp.ne']
    have hxpos : 0 < F x := lt_of_le_of_ne (hFn x) (Ne.symm hx)
    have hfun : (Ioi (0 : ℝ)).indicator (fun t => H t x) =
        (Ioi (B * F x)).indicator
          (fun t => ENNReal.ofReal (t ^ (p - q - 1)) * ENNReal.ofReal ((F x) ^ q)) := by
      funext t
      by_cases hx' : B * F x < t
      · have ht : 0 < t := (mul_nonneg hB.le (hFn x)).trans_lt hx'
        simp [H, ht, hx']
      · simp [H, hx']
    rw [← lintegral_indicator measurableSet_Ioi, hfun,
      lintegral_indicator measurableSet_Ioi, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      e2_lintegral_power_tail hpq (mul_pos hB hxpos),
      ← ENNReal.ofReal_mul (div_nonneg
        (Real.rpow_nonneg (mul_nonneg hB.le (hFn x)) _) (by linarith)),
      ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hB.le _) (by linarith))]
    congr 1
    rw [Real.mul_rpow hB.le (hFn x)]
    have hh : (F x) ^ (p - q) * (F x) ^ q = (F x) ^ p := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    calc
      B ^ (p - q) * (F x) ^ (p - q) / (q - p) * (F x) ^ q =
          (B ^ (p - q) / (q - p)) * ((F x) ^ (p - q) * (F x) ^ q) := by ring
      _ = _ := by rw [hh]
  simp_rw [hinner]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PlanarNikodym
