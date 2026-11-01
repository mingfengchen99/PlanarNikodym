import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Tactic

/-! Real-variable interpolation between strong L² and L∞ bounds. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

/-- The one-variable integral needed in the L²/L∞ truncation argument. -/
theorem endpoint_lintegral_power {p a : ℝ} (hp : 2 < p) (ha : 0 ≤ a) :
    (∫⁻ t in Ioc 0 a, ENNReal.ofReal (t ^ (p - 3))) =
      ENNReal.ofReal (a ^ (p - 2) / (p - 2)) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (p - 3)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 a)] (fun t : ℝ => t ^ (p - 3)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1 hnn,
    ← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl (by linarith))]
  have he : p - 3 + 1 = p - 2 := by ring
  rw [he, Real.zero_rpow (by linarith : p - 2 ≠ 0), sub_zero]

/-- Tonelli computes the integrated truncated square exactly. This is the
analytic step that turns a distribution-function estimate into strong Lp. -/
theorem endpoint_truncated_square_layercake
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {F : α → ℝ} (hF : Measurable F) (hFn : ∀ x, 0 ≤ F x)
    {p B : ℝ} (hp : 2 < p) (hB : 0 < B) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 3)) *
      ∫⁻ x, ({x | t ≤ B * F x}.indicator (fun x => ENNReal.ofReal ((F x) ^ 2))) x ∂μ) =
      ENNReal.ofReal (B ^ (p - 2) / (p - 2)) *
        ∫⁻ x, ENNReal.ofReal ((F x) ^ p) ∂μ := by
  classical
  let H : ℝ → α → ℝ≥0∞ := fun t x =>
    {z : ℝ × α | z.1 ≤ B * F z.2}.indicator
      (fun z => ENNReal.ofReal (z.1 ^ (p - 3)) * ENNReal.ofReal ((F z.2) ^ 2)) (t, x)
  have hHm : Measurable (Function.uncurry H) := by
    apply Measurable.indicator
    · exact (measurable_fst.pow_const _).ennreal_ofReal.mul
        ((hF.comp measurable_snd).pow_const 2).ennreal_ofReal
    · exact measurableSet_le measurable_fst (measurable_const.mul (hF.comp measurable_snd))
  have he (t : ℝ) : ENNReal.ofReal (t ^ (p - 3)) *
      (∫⁻ x, ({x | t ≤ B * F x}.indicator (fun x => ENNReal.ofReal ((F x) ^ 2))) x ∂μ) =
      ∫⁻ x, H t x ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    by_cases hx : t ≤ B * F x <;> simp [H, hx]
  simp_rw [he]
  rw [lintegral_lintegral_swap hHm.aemeasurable]
  have hinner (x : α) : (∫⁻ t in Ioi (0 : ℝ), H t x) =
      ENNReal.ofReal (B ^ (p - 2) / (p - 2)) * ENNReal.ofReal ((F x) ^ p) := by
    have hfun : (Ioi (0 : ℝ)).indicator (fun t => H t x) =
        (Ioc 0 (B * F x)).indicator
          (fun t => ENNReal.ofReal (t ^ (p - 3)) * ENNReal.ofReal ((F x) ^ 2)) := by
      funext t
      by_cases ht : 0 < t <;> by_cases hx : t ≤ B * F x <;> simp [H, ht, hx]
    rw [← lintegral_indicator measurableSet_Ioi, hfun,
      lintegral_indicator measurableSet_Ioc, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      endpoint_lintegral_power hp (mul_nonneg hB.le (hFn x)),
      ← ENNReal.ofReal_mul (div_nonneg
        (Real.rpow_nonneg (mul_nonneg hB.le (hFn x)) _) (by linarith))]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hB.le _) (by linarith))]
    congr 1
    rw [Real.mul_rpow hB.le (hFn x)]
    by_cases hx : F x = 0
    · simp [hx, Real.zero_rpow (by linarith : p - 2 ≠ 0), Real.zero_rpow (by linarith : p ≠ 0)]
    · have hxpos : 0 < F x := lt_of_le_of_ne (hFn x) (Ne.symm hx)
      rw [← Real.rpow_natCast (F x) 2]
      have hh : (F x) ^ (p - 2) * (F x) ^ (2 : ℝ) = (F x) ^ p := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      calc
        B ^ (p - 2) * (F x) ^ (p - 2) / (p - 2) * (F x) ^ (2 : ℝ) =
            (B ^ (p - 2) / (p - 2)) * ((F x) ^ (p - 2) * (F x) ^ (2 : ℝ)) := by ring
        _ = _ := by rw [hh]
  simp_rw [hinner]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Above a positive truncation level, an Lp input with p>2 belongs to
L², including on spaces of infinite measure. -/
theorem endpoint_high_truncation_square_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hfm : Measurable f) {p a : ℝ} (hp : 2 < p) (ha : 0 < a)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) μ) :
    Integrable (fun x => ‖({x | a ≤ ‖f x‖}.indicator f) x‖ ^ 2) μ := by
  classical
  have hs : MeasurableSet {x | a ≤ ‖f x‖} := measurableSet_le measurable_const hfm.norm
  have hm := (hfm.indicator hs).norm.pow_const 2
  apply (hfp.const_mul (a ^ (2 - p))).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : a ≤ ‖f x‖
  · rw [Set.indicator_of_mem (show x ∈ {x | a ≤ ‖f x‖} from hx)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖f x‖))]
    have hxpos : 0 < ‖f x‖ := ha.trans_le hx
    have he : ‖f x‖ ^ 2 = ‖f x‖ ^ (2 - p) * ‖f x‖ ^ p := by
      rw [← Real.rpow_add hxpos]
      norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hx (by linarith))
      (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [Set.indicator_of_notMem (show x ∉ {x | a ≤ ‖f x‖} from hx)]
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- Square-integral Chebyshev in a form suitable for interpolation. -/
theorem endpoint_measure_tail_le_square
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    {g : β → ℂ} (hg : Measurable g) {t : ℝ} (ht : 0 < t) :
    ν {y | t ≤ ‖g y‖} ≤ ENNReal.ofReal ((t ^ 2)⁻¹) *
      ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) ∂ν := by
  have hM := mul_meas_ge_le_lintegral₀
    ((hg.norm.pow_const 2).ennreal_ofReal.aemeasurable (μ := ν)) (ENNReal.ofReal (t ^ 2))
  have he : {y | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (‖g y‖ ^ 2)} =
      {y | t ≤ ‖g y‖} := by
    ext y
    simp only [mem_setOf_eq, ENNReal.ofReal_le_ofReal_iff (sq_nonneg _),
      sq_le_sq₀ ht.le (norm_nonneg _)]
  rw [he] at hM
  have hn : ENNReal.ofReal (t ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ht)).ne'
  calc
    _ = (ENNReal.ofReal (t ^ 2))⁻¹ * (ENNReal.ofReal (t ^ 2) * ν {y | t ≤ ‖g y‖}) :=
      (ENNReal.inv_mul_cancel_left hn ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal (t ^ 2))⁻¹ *
        ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) ∂ν := mul_le_mul_right hM _
    _ = _ := by rw [ENNReal.ofReal_inv_of_pos (sq_pos_of_pos ht)]

/-- Strong L² and the pointwise L∞ endpoint give the quantitative
truncation estimate for the distribution of the actual operator output. -/
theorem endpoint_operator_tail_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (T : (α → ℂ) → β → ℂ)
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    (hm : ∀ g, Integrable g μ → Measurable (T g))
    {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 < B)
    (h2 : ∀ g, Integrable g μ → Integrable (fun x => ‖g x‖ ^ 2) μ →
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ)
    (hinf : ∀ g, Integrable g μ → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖g x‖ ≤ M) →
      ∀ y, ‖T g y‖ ≤ B * M)
    {f : α → ℂ} (hf : Integrable f μ) (hfm : Measurable f)
    {p : ℝ} (hp : 2 < p) (hfp : Integrable (fun x => ‖f x‖ ^ p) μ)
    {t : ℝ} (ht : 0 < t) :
    ν {y | t ≤ ‖T f y‖} ≤ ENNReal.ofReal (4 * A / t ^ 2) *
      ∫⁻ x, ({x | t ≤ (2 * B) * ‖f x‖}.indicator
        (fun x => ENNReal.ofReal (‖f x‖ ^ 2))) x ∂μ := by
  classical
  let a := t / (2 * B)
  have ha : 0 < a := div_pos ht (by positivity)
  let S := {x | a ≤ ‖f x‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const hfm.norm
  let g := S.indicator f
  let h := Sᶜ.indicator f
  have hgi : Integrable g μ := hf.indicator hS
  have hhi : Integrable h μ := hf.indicator hS.compl
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    endpoint_high_truncation_square_integrable hfm hp ha hfp
  have hhb : ∀ x, ‖h x‖ ≤ a := by
    intro x
    by_cases hx : x ∈ S
    · simp only [h, indicator_of_notMem (notMem_compl_iff.mpr hx), norm_zero]
      exact ha.le
    · simp only [h, indicator_of_mem (show x ∈ Sᶜ from hx)]
      exact le_of_lt (lt_of_not_ge hx)
  have hsum : (fun x => h x + g x) = f := by
    funext x
    by_cases hx : x ∈ S <;> simp [h, g, hx]
  have hlow (y : β) : ‖T h y‖ ≤ t / 2 := by
    have hh := hinf h hhi a ha.le hhb y
    have he : B * a = t / 2 := by dsimp [a]; field_simp
    rwa [he] at hh
  have hsub : {y | t ≤ ‖T f y‖} ⊆ {y | t / 2 ≤ ‖T g y‖} := by
    intro y hy
    have hs : T f y = T h y + T g y := by rw [← hsum]; exact hadd h g hhi hgi y
    have hh := norm_add_le (T h y) (T g y)
    rw [← hs] at hh
    have hl := hlow y
    change t ≤ ‖T f y‖ at hy
    change t / 2 ≤ ‖T g y‖
    linarith
  have hgId : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ) =
      ∫⁻ x, ({x | t ≤ (2 * B) * ‖f x‖}.indicator
        (fun x => ENNReal.ofReal (‖f x‖ ^ 2))) x ∂μ := by
    apply lintegral_congr
    intro x
    have he : x ∈ S ↔ t ≤ (2 * B) * ‖f x‖ := by
      change t / (2 * B) ≤ ‖f x‖ ↔ _
      rw [div_le_iff₀ (by positivity : 0 < 2 * B)]
      rw [mul_comm (‖f x‖)]
    by_cases hx : x ∈ S
    · simp [g, hx, he.mp hx]
    · simp [g, hx, mt he.mpr hx]
  calc
    _ ≤ ν {y | t / 2 ≤ ‖T g y‖} := measure_mono hsub
    _ ≤ ENNReal.ofReal (((t / 2) ^ 2)⁻¹) *
        ∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ 2) ∂ν :=
      endpoint_measure_tail_le_square ν (hm g hgi) (by positivity)
    _ ≤ ENNReal.ofReal (((t / 2) ^ 2)⁻¹) *
        (ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ) :=
      mul_le_mul_right (h2 g hgi hg2) _
    _ = _ := by
      rw [hgId, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
      ring

/-- Strong L² and L∞ interpolation for p>2, proved by truncating the
input, Chebyshev, layer cake and Tonelli. The displayed constant has the
correct powers of both actual endpoint constants. -/
theorem strong_L2_LInfinity_interpolation_integral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : Measure β) (T : (α → ℂ) → β → ℂ)
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    (hm : ∀ g, Integrable g μ → Measurable (T g))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (h2 : ∀ g, Integrable g μ → Integrable (fun x => ‖g x‖ ^ 2) μ →
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ)
    (hinf : ∀ g, Integrable g μ → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖g x‖ ≤ M) →
      ∀ y, ‖T g y‖ ≤ B * M)
    {f : α → ℂ} (hf : Integrable f μ) (hfm : Measurable f)
    {p : ℝ} (hp : 2 < p) (hfp : Integrable (fun x => ‖f x‖ ^ p) μ) :
    (∫⁻ y, ENNReal.ofReal (‖T f y‖ ^ p) ∂ν) ≤
      ENNReal.ofReal (4 * p * A * (2 * B) ^ (p - 2) / (p - 2)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p) ∂μ := by
  classical
  let J : ℝ → ℝ≥0∞ := fun t => ∫⁻ x,
    ({x | t ≤ (2 * B) * ‖f x‖}.indicator (fun x => ENNReal.ofReal (‖f x‖ ^ 2))) x ∂μ
  have htail (t : ℝ) (ht : 0 < t) :
      ν {y | t ≤ ‖T f y‖} ≤ ENNReal.ofReal (4 * A / t ^ 2) * J t :=
    endpoint_operator_tail_bound μ ν T hadd hm hA hB h2 hinf hf hfm hp hfp ht
  have hweight (t : ℝ) (ht : 0 < t) :
      (ENNReal.ofReal (4 * A / t ^ 2) * J t) * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (4 * A) * (ENNReal.ofReal (t ^ (p - 3)) * J t) := by
    have he : (4 * A / t ^ 2) * t ^ (p - 1) = 4 * A * t ^ (p - 3) := by
      have hpw : t ^ (p - 3) = t ^ (p - 1) / t ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast t 2, ← Real.rpow_sub ht]
        congr 1
        ring
      rw [hpw]
      ring
    calc
      _ = (ENNReal.ofReal (4 * A / t ^ 2) * ENNReal.ofReal (t ^ (p - 1))) * J t := by ac_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), he,
          ENNReal.ofReal_mul (by positivity)]
        ac_rfl
  rw [lintegral_rpow_eq_lintegral_meas_le_mul ν
    (Filter.Eventually.of_forall (fun y => norm_nonneg (T f y)))
    (hm f hf).norm.aemeasurable (by linarith : 0 < p)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        (ENNReal.ofReal (4 * A / t ^ 2) * J t) * ENNReal.ofReal (t ^ (p - 1)) := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_le_mul_left (htail t ht) _
    _ = ENNReal.ofReal p * (ENNReal.ofReal (4 * A) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 3)) * J t) := by
      congr 1
      calc
        _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (4 * A) *
            (ENNReal.ofReal (t ^ (p - 3)) * J t) := by
          apply lintegral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hweight t ht
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      rw [endpoint_truncated_square_layercake μ hfm.norm (fun x => norm_nonneg (f x))
        hp (by positivity : 0 < 2 * B)]
      rw [← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ p),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

/-- A strong L² bound makes the operator independent of the chosen
representative, almost everywhere, using only additivity on L¹ inputs. -/
theorem endpoint_operator_congr_ae
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (T : (α → ℂ) → β → ℂ)
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    (hm : ∀ g, Integrable g μ → Measurable (T g))
    {A : ℝ}
    (h2 : ∀ g, Integrable g μ → Integrable (fun x => ‖g x‖ ^ 2) μ →
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ)
    {f g : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : f =ᵐ[μ] g) : T f =ᵐ[ν] T g := by
  let h : α → ℂ := fun x => f x - g x
  have hi : Integrable h μ := hf.sub hg
  have hz : h =ᵐ[μ] 0 := hfg.mono (fun x hx => by simp [h, hx])
  have hs0 : (fun x => ‖h x‖ ^ 2) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hz] with x hx
    simp [hx]
  have hi2 : Integrable (fun x => ‖h x‖ ^ 2) μ :=
    (integrable_zero α ℝ μ).congr hs0.symm
  have hzero : (∫⁻ y, ENNReal.ofReal (‖T h y‖ ^ 2) ∂ν) = 0 := by
    apply le_antisymm _ zero_le
    have hb := h2 h hi hi2
    have hI : (∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) ∂μ) = 0 := by
      have he : (fun x => ENNReal.ofReal (‖h x‖ ^ 2)) =ᵐ[μ] (fun _ => (0 : ℝ≥0∞)) := by
        filter_upwards [hs0] with x hx
        simp [hx]
      rw [lintegral_congr_ae he]
      simp
    simpa only [hI, mul_zero] using hb
  have hTh : ∀ᵐ y ∂ν, ENNReal.ofReal (‖T h y‖ ^ 2) = 0 :=
    (lintegral_eq_zero_iff ((hm h hi).norm.pow_const 2).ennreal_ofReal).mp hzero
  filter_upwards [hTh] with y hy
  have hn : T h y = 0 := by
    have hsq : ‖T h y‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hy
    have : ‖T h y‖ = 0 := by nlinarith [norm_nonneg (T h y)]
    exact norm_eq_zero.mp this
  have he : (fun x => h x + g x) = f := by funext x; dsimp [h]; ring
  have hh := hadd h g hi hg y
  rw [he, hn, zero_add] at hh
  exact hh

/-- Integral formula for a positive real exponent on an arbitrary measure
space, retaining the actual real norm inside the nonnegative integral. -/
theorem endpoint_eLpNorm_eq_power_integral
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) (u : X → ℂ)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm u (ENNReal.ofReal p) ρ =
      (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ p) ∂ρ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  congr 1
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

/-- Standard Lp operator estimate for arbitrary L¹∩Lp representatives.
No pointwise measurability hypothesis on the input is required. -/
theorem strong_L2_LInfinity_interpolation
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : Measure β) (T : (α → ℂ) → β → ℂ)
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    (hm : ∀ g, Integrable g μ → Measurable (T g))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (h2 : ∀ g, Integrable g μ → Integrable (fun x => ‖g x‖ ^ 2) μ →
      (∫⁻ y, ENNReal.ofReal (‖T g y‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ)
    (hinf : ∀ g, Integrable g μ → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖g x‖ ≤ M) →
      ∀ y, ‖T g y‖ ≤ B * M)
    {f : α → ℂ} (hf : Integrable f μ)
    {p : ℝ} (hp : 2 < p) (hfp : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm (T f) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal ((4 * p * A * (2 * B) ^ (p - 2) / (p - 2)) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) μ := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgi : Integrable g μ := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgp : MemLp g (ENNReal.ofReal p) μ := (memLp_congr_ae hfg).mp hfp
  have hp0 : 0 < p := by linarith
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpn : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hgpow : Integrable (fun x => ‖g x‖ ^ p) μ := by
    simpa only [hpr] using hgp.integrable_norm_rpow hpn ENNReal.ofReal_ne_top
  have hint := strong_L2_LInfinity_interpolation_integral μ ν T hadd hm hA hB h2 hinf
    hgi hgm hp hgpow
  rw [eLpNorm_congr_ae (endpoint_operator_congr_ae μ ν T hadd hm h2 hf hgi hfg),
    eLpNorm_congr_ae hfg, endpoint_eLpNorm_eq_power_integral ν (T g) hp0,
    endpoint_eLpNorm_eq_power_integral μ g hp0]
  have hC : 0 ≤ 4 * p * A * (2 * B) ^ (p - 2) / (p - 2) := by positivity
  calc
    _ ≤ (ENNReal.ofReal (4 * p * A * (2 * B) ^ (p - 2) / (p - 2)) *
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ p) ∂μ) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hint (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ENNReal.ofReal_rpow_of_nonneg hC (by positivity)]

end PlanarNikodym
