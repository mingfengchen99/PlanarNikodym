import PlanarNikodym.Analysis.Fourier.GlyzSmoothTruncation
import PlanarNikodym.Analysis.Fourier.EndpointInterpolation

/-! Real operator interpolation for finite Schwartz families. Smooth
amplitude truncations preserve the input space. This theorem interpolates
an actual linear operator, rather than the norms of individual inputs. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace PlanarNikodym

theorem glyz_lintegral_power_interval {p q a : ℝ} (hpq : q < p) (ha : 0 ≤ a) :
    (∫⁻ t in Ioc 0 a, ENNReal.ofReal (t ^ (p - q - 1))) =
      ENNReal.ofReal (a ^ (p - q) / (p - q)) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (p - q - 1)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 a)] (fun t : ℝ => t ^ (p - q - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1 hnn,
    ← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl (by linarith))]
  have he : p - q - 1 + 1 = p - q := by ring
  rw [he, Real.zero_rpow (by linarith : p - q ≠ 0), sub_zero]

theorem glyz_truncated_power_layercake
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {F : α → ℝ} (hF : Measurable F) (hFn : ∀ x, 0 ≤ F x)
    {p q B : ℝ} (hq : 0 < q) (hpq : q < p) (hB : 0 < B) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q - 1)) *
      ∫⁻ x, ({x | t ≤ B * F x}.indicator (fun x => ENNReal.ofReal ((F x) ^ q))) x ∂μ) =
      ENNReal.ofReal (B ^ (p - q) / (p - q)) *
        ∫⁻ x, ENNReal.ofReal ((F x) ^ p) ∂μ := by
  classical
  let H : ℝ → α → ℝ≥0∞ := fun t x =>
    {z : ℝ × α | z.1 ≤ B * F z.2}.indicator
      (fun z => ENNReal.ofReal (z.1 ^ (p - q - 1)) * ENNReal.ofReal ((F z.2) ^ q)) (t, x)
  have hHm : Measurable (Function.uncurry H) := by
    apply Measurable.indicator
    · exact (measurable_fst.pow_const _).ennreal_ofReal.mul
        ((hF.comp measurable_snd).pow_const q).ennreal_ofReal
    · exact measurableSet_le measurable_fst (measurable_const.mul (hF.comp measurable_snd))
  have he (t : ℝ) : ENNReal.ofReal (t ^ (p - q - 1)) *
      (∫⁻ x, ({x | t ≤ B * F x}.indicator (fun x => ENNReal.ofReal ((F x) ^ q))) x ∂μ) =
      ∫⁻ x, H t x ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    by_cases hx : t ≤ B * F x <;> simp [H, hx]
  simp_rw [he]
  rw [lintegral_lintegral_swap hHm.aemeasurable]
  have hinner (x : α) : (∫⁻ t in Ioi (0 : ℝ), H t x) =
      ENNReal.ofReal (B ^ (p - q) / (p - q)) * ENNReal.ofReal ((F x) ^ p) := by
    have hfun : (Ioi (0 : ℝ)).indicator (fun t => H t x) =
        (Ioc 0 (B * F x)).indicator
          (fun t => ENNReal.ofReal (t ^ (p - q - 1)) * ENNReal.ofReal ((F x) ^ q)) := by
      funext t
      by_cases ht : 0 < t <;> by_cases hx : t ≤ B * F x <;> simp [H, ht, hx]
    rw [← lintegral_indicator measurableSet_Ioi, hfun,
      lintegral_indicator measurableSet_Ioc, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      glyz_lintegral_power_interval hpq (mul_nonneg hB.le (hFn x)),
      ← ENNReal.ofReal_mul (div_nonneg
        (Real.rpow_nonneg (mul_nonneg hB.le (hFn x)) _) (by linarith))]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hB.le _) (by linarith))]
    congr 1
    rw [Real.mul_rpow hB.le (hFn x)]
    by_cases hx : F x = 0
    · simp [hx, Real.zero_rpow (by linarith : p - q ≠ 0),
        Real.zero_rpow (by linarith : p ≠ 0), Real.zero_rpow hq.ne']
    · have hxpos : 0 < F x := lt_of_le_of_ne (hFn x) (Ne.symm hx)
      have hh : (F x) ^ (p - q) * (F x) ^ q = (F x) ^ p := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      calc
        B ^ (p - q) * (F x) ^ (p - q) / (p - q) * (F x) ^ q =
            (B ^ (p - q) / (p - q)) * ((F x) ^ (p - q) * (F x) ^ q) := by ring
        _ = _ := by rw [hh]
  simp_rw [hinner]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem glyz_measure_tail_le_power
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    {g : β → ℂ} (hg : Measurable g) {q t : ℝ} (hq : 0 < q) (ht : 0 < t) :
    ν {y | t ≤ ‖g y‖} ≤ ENNReal.ofReal ((t ^ q)⁻¹) *
      ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ q) ∂ν := by
  have hM := mul_meas_ge_le_lintegral₀
    ((hg.norm.pow_const q).ennreal_ofReal.aemeasurable (μ := ν)) (ENNReal.ofReal (t ^ q))
  have he : {y | ENNReal.ofReal (t ^ q) ≤ ENNReal.ofReal (‖g y‖ ^ q)} =
      {y | t ≤ ‖g y‖} := by
    ext y
    simp only [mem_setOf_eq, ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow_iff ht.le (norm_nonneg _) hq
  rw [he] at hM
  have hn : ENNReal.ofReal (t ^ q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ht q)).ne'
  calc
    _ = (ENNReal.ofReal (t ^ q))⁻¹ * (ENNReal.ofReal (t ^ q) * ν {y | t ≤ ‖g y‖}) :=
      (ENNReal.inv_mul_cancel_left hn ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal (t ^ q))⁻¹ *
        ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ q) ∂ν := mul_le_mul_right hM _
    _ = _ := by rw [ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ht q)]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem glyz_schwartz_operator_tail
    {ι : Type*} [Fintype ι]
    (T : (ι → SchwartzMap E ℂ) →ₗ[ℂ] SchwartzMap F ℂ)
    {q A B : ℝ} (hq : 0 < q) (_hA : 0 ≤ A) (hB : 0 < B)
    (hcrit : ∀ g : ι → SchwartzMap E ℂ,
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ q)) ≤
        ENNReal.ofReal A * ∑ i, ∫⁻ x, ENNReal.ofReal (‖g i x‖ ^ q))
    (hinf : ∀ g : ι → SchwartzMap E ℂ, ∀ M : ℝ, 0 ≤ M →
      (∀ i x, ‖g i x‖ ≤ M) → ∀ y, ‖T g y‖ ≤ B * M)
    (f : ι → SchwartzMap E ℂ) {t : ℝ} (ht : 0 < t) :
    volume {y | t ≤ ‖T f y‖} ≤ ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) *
      ∑ i, ∫⁻ x, ({x | t ≤ (4 * B) * ‖f i x‖}.indicator
        (fun x => ENNReal.ofReal (‖f i x‖ ^ q))) x := by
  classical
  let a := t / (4 * B)
  have ha : 0 < a := div_pos ht (by positivity)
  let lo : ι → SchwartzMap E ℂ := fun i => glyzSchwartzLow a ha (f i)
  let hi : ι → SchwartzMap E ℂ := fun i => glyzSchwartzHigh a ha (f i)
  have hsum : lo + hi = f := funext fun i => glyzSchwartzLow_add_high a ha (f i)
  have hlow (y : F) : ‖T lo y‖ ≤ t / 2 := by
    have h := hinf lo (2 * a) (by positivity)
      (fun i x => norm_glyzSchwartzLow_le a ha (f i) x) y
    have he : B * (2 * a) = t / 2 := by dsimp [a]; field_simp; ring
    rwa [he] at h
  have hsub : {y | t ≤ ‖T f y‖} ⊆ {y | t / 2 ≤ ‖T hi y‖} := by
    intro y hy
    have he : T f y = T lo y + T hi y := by rw [← hsum, T.map_add]; rfl
    have hh := norm_add_le (T lo y) (T hi y)
    rw [← he] at hh
    have hl := hlow y
    change t ≤ ‖T f y‖ at hy
    change t / 2 ≤ ‖T hi y‖
    linarith
  have hhigh (i : ι) :
      (∫⁻ x, ENNReal.ofReal (‖hi i x‖ ^ q)) ≤
        ∫⁻ x, ({x | t ≤ (4 * B) * ‖f i x‖}.indicator
          (fun x => ENNReal.ofReal (‖f i x‖ ^ q))) x := by
    apply lintegral_mono
    intro x
    by_cases hx : t ≤ (4 * B) * ‖f i x‖
    · rw [indicator_of_mem (show x ∈ {x | t ≤ (4 * B) * ‖f i x‖} from hx)]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (norm_nonneg _) (norm_glyzSchwartzHigh_le a ha (f i) x) hq.le)
    · rw [indicator_of_notMem (show x ∉ {x | t ≤ (4 * B) * ‖f i x‖} from hx)]
      have hx' : ‖f i x‖ ≤ a := by
        dsimp [a]
        exact (le_div_iff₀ (by positivity : 0 < 4 * B)).mpr (by nlinarith)
      simp only [hi, glyzSchwartzHigh_eq_zero a ha (f i) hx', norm_zero,
        Real.zero_rpow hq.ne', ENNReal.ofReal_zero, le_refl]
  calc
    _ ≤ volume {y | t / 2 ≤ ‖T hi y‖} := measure_mono hsub
    _ ≤ ENNReal.ofReal (((t / 2) ^ q)⁻¹) *
        ∫⁻ y, ENNReal.ofReal (‖T hi y‖ ^ q) :=
      glyz_measure_tail_le_power volume (T hi).continuous.measurable hq (by positivity)
    _ ≤ ENNReal.ofReal (((t / 2) ^ q)⁻¹) *
        (ENNReal.ofReal A * ∑ i, ∫⁻ x, ENNReal.ofReal (‖hi i x‖ ^ q)) :=
      mul_le_mul_right (hcrit hi) _
    _ ≤ ENNReal.ofReal (((t / 2) ^ q)⁻¹) *
        (ENNReal.ofReal A * ∑ i, ∫⁻ x, ({x | t ≤ (4 * B) * ‖f i x‖}.indicator
          (fun x => ENNReal.ofReal (‖f i x‖ ^ q))) x) :=
      mul_le_mul_right (mul_le_mul_right (Finset.sum_le_sum fun i _ => hhigh i) _) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.div_rpow ht.le (by norm_num), inv_div]
      ring

theorem glyz_schwartz_q_infinity_interpolation
    {ι : Type*} [Fintype ι]
    (T : (ι → SchwartzMap E ℂ) →ₗ[ℂ] SchwartzMap F ℂ)
    {p q A B : ℝ} (hq : 0 < q) (hpq : q < p) (hA : 0 ≤ A) (hB : 0 < B)
    (hcrit : ∀ g : ι → SchwartzMap E ℂ,
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ q)) ≤
        ENNReal.ofReal A * ∑ i, ∫⁻ x, ENNReal.ofReal (‖g i x‖ ^ q))
    (hinf : ∀ g : ι → SchwartzMap E ℂ, ∀ M : ℝ, 0 ≤ M →
      (∀ i x, ‖g i x‖ ≤ M) → ∀ y, ‖T g y‖ ≤ B * M)
    (f : ι → SchwartzMap E ℂ) :
    (∫⁻ y, ENNReal.ofReal (‖T f y‖ ^ p)) ≤
      ENNReal.ofReal (p * (2 : ℝ) ^ q * A * (4 * B) ^ (p - q) / (p - q)) *
        ∑ i, ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ p) := by
  classical
  let J : ℝ → ℝ≥0∞ := fun t => ∑ i, ∫⁻ x,
    ({x | t ≤ (4 * B) * ‖f i x‖}.indicator (fun x => ENNReal.ofReal (‖f i x‖ ^ q))) x
  have htail (t : ℝ) (ht : 0 < t) :
      volume {y | t ≤ ‖T f y‖} ≤ ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) * J t :=
    glyz_schwartz_operator_tail T hq hA hB hcrit hinf f ht
  have hweight (t : ℝ) (ht : 0 < t) :
      (ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) * J t) * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal ((2 : ℝ) ^ q * A) * (ENNReal.ofReal (t ^ (p - q - 1)) * J t) := by
    have he : ((2 : ℝ) ^ q * A / t ^ q) * t ^ (p - 1) =
        (2 : ℝ) ^ q * A * t ^ (p - q - 1) := by
      have hpw : t ^ (p - q - 1) = t ^ (p - 1) / t ^ q := by
        rw [← Real.rpow_sub ht]
        congr 1
        ring
      rw [hpw]
      ring
    calc
      _ = (ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) *
          ENNReal.ofReal (t ^ (p - 1))) * J t := by ac_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), he,
          ENNReal.ofReal_mul (by positivity)]
        ac_rfl
  have hlayer :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q - 1)) * J t) =
      ENNReal.ofReal ((4 * B) ^ (p - q) / (p - q)) *
        ∑ i, ∫⁻ x, ENNReal.ofReal (‖f i x‖ ^ p) := by
    simp_rw [J, Finset.mul_sum]
    rw [lintegral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ =>
        glyz_truncated_power_layercake volume (f i).continuous.measurable.norm
          (fun x => norm_nonneg (f i x)) hq hpq (by positivity)
    · intro i _
      exact Measurable.mul (measurable_id.pow_const _).ennreal_ofReal
        (Measurable.lintegral_prod_right (by
          apply Measurable.indicator
          · exact (((f i).continuous.measurable.comp measurable_snd).norm.pow_const q).ennreal_ofReal
          · exact measurableSet_le measurable_fst
              (measurable_const.mul ((f i).continuous.measurable.comp measurable_snd).norm)))
  rw [lintegral_rpow_eq_lintegral_meas_le_mul volume
    (Filter.Eventually.of_forall (fun y => norm_nonneg (T f y)))
    (T f).continuous.measurable.norm.aemeasurable (hq.trans hpq)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        (ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) * J t) * ENNReal.ofReal (t ^ (p - 1)) := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_le_mul_left (htail t ht) _
    _ = ENNReal.ofReal p * (ENNReal.ofReal ((2 : ℝ) ^ q * A) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q - 1)) * J t) := by
      congr 1
      calc
        _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((2 : ℝ) ^ q * A) *
            (ENNReal.ofReal (t ^ (p - q - 1)) * J t) := by
          apply lintegral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hweight t ht
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      rw [hlayer, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (hq.trans hpq).le,
        ← ENNReal.ofReal_mul (mul_nonneg (hq.trans hpq).le
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hA))]
      congr 2
      ring

end PlanarNikodym
