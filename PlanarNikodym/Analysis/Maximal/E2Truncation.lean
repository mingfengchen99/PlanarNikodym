import PlanarNikodym.Analysis.Fourier.GlyzSchwartzInterpolation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual truncation argument for two finite endpoint exponents.
The input class is L¹ ∩ Lᵖ, so both truncations retain the integrability
needed to define the curve operators before frequency localization. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem e2_high_truncation_integrable_power
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hfm : Measurable f) {p q a : ℝ}
    (hq : 0 < q) (hqp : q < p) (ha : 0 < a)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) μ) :
    Integrable (fun x => ‖({x | a ≤ ‖f x‖}.indicator f) x‖ ^ q) μ := by
  classical
  have hs : MeasurableSet {x | a ≤ ‖f x‖} := measurableSet_le measurable_const hfm.norm
  have hm := (hfm.indicator hs).norm.pow_const q
  apply (hfp.const_mul (a ^ (q - p))).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : a ≤ ‖f x‖
  · rw [Set.indicator_of_mem (show x ∈ {x | a ≤ ‖f x‖} from hx)]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have hxpos : 0 < ‖f x‖ := ha.trans_le hx
    have he : ‖f x‖ ^ q = ‖f x‖ ^ (q - p) * ‖f x‖ ^ p := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hx (by linarith))
      (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [Set.indicator_of_notMem (show x ∉ {x | a ≤ ‖f x‖} from hx)]
    simp only [norm_zero, Real.zero_rpow hq.ne', norm_zero]
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem e2_low_truncation_integrable_power
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hfm : Measurable f) {p q a : ℝ}
    (hp : 0 < p) (hpq : p < q) (ha : 0 < a)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) μ) :
    Integrable (fun x => ‖({x | a ≤ ‖f x‖}ᶜ.indicator f) x‖ ^ q) μ := by
  classical
  have hs : MeasurableSet {x | a ≤ ‖f x‖} := measurableSet_le measurable_const hfm.norm
  have hm := (hfm.indicator hs.compl).norm.pow_const q
  apply (hfp.const_mul (a ^ (q - p))).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : a ≤ ‖f x‖
  · simp only [Set.indicator_of_notMem (show x ∉ {x | a ≤ ‖f x‖}ᶜ from not_not.mpr hx),
      norm_zero, Real.zero_rpow (by linarith : q ≠ 0), norm_zero]
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  · rw [Set.indicator_of_mem (show x ∈ {x | a ≤ ‖f x‖}ᶜ from hx)]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hz : ‖f x‖ = 0
    · simp [hz, Real.zero_rpow hp.ne', Real.zero_rpow (by linarith : q ≠ 0)]
    · have hxpos : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have he : ‖f x‖ ^ q = ‖f x‖ ^ (q - p) * ‖f x‖ ^ p := by
        rw [← Real.rpow_add hxpos]; congr 1; ring
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) (le_of_not_ge hx) (by linarith))
        (Real.rpow_nonneg (norm_nonneg _) _)

/-- Chebyshev, subadditivity, and the two genuine amplitude truncations.
The endpoint constants multiply integrals of powers, rather than norms. -/
theorem e2_sublinear_two_endpoint_tail
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (T : (α → ℂ) → β → ℂ)
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
    (hfp : Integrable (fun x => ‖f x‖ ^ p) μ) {t : ℝ} (ht : 0 < t) :
    ν {y | t ≤ ‖T f y‖} ≤
      ENNReal.ofReal ((2 : ℝ) ^ q₀ * A₀ / t ^ q₀) *
        ∫⁻ x, ({x | t ≤ B * ‖f x‖}.indicator
          (fun x => ENNReal.ofReal (‖f x‖ ^ q₀))) x ∂μ +
      ENNReal.ofReal ((2 : ℝ) ^ q₁ * A₁ / t ^ q₁) *
        ∫⁻ x, ({x | B * ‖f x‖ < t}.indicator
          (fun x => ENNReal.ofReal (‖f x‖ ^ q₁))) x ∂μ := by
  classical
  let S := {x | t / B ≤ ‖f x‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const hfm.norm
  let g := S.indicator f
  let h := Sᶜ.indicator f
  have hgi : Integrable g μ := hf.indicator hS
  have hhi' : Integrable h μ := hf.indicator hS.compl
  have hsum : g + h = f := by funext x; by_cases hx : x ∈ S <;> simp [g, h, hx]
  have hsplit : {y | t ≤ ‖T f y‖} ⊆
      {y | t / 2 ≤ ‖T g y‖} ∪ {y | t / 2 ≤ ‖T h y‖} := by
    intro y hy
    have hh := hsub g h hgi hhi' y
    rw [hsum] at hh
    change t ≤ ‖T f y‖ at hy
    change t / 2 ≤ ‖T g y‖ ∨ t / 2 ≤ ‖T h y‖
    by_contra hc
    push Not at hc
    linarith
  have hbound (u : α → ℂ) (hu : Integrable u μ) (q A : ℝ)
      (hq : 0 < q) (hA : 0 ≤ A)
      (hb : (∫⁻ y, ENNReal.ofReal (‖T u y‖ ^ q) ∂ν) ≤
        ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ q) ∂μ) :
      ν {y | t / 2 ≤ ‖T u y‖} ≤ ENNReal.ofReal ((2 : ℝ) ^ q * A / t ^ q) *
        ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ q) ∂μ := by
    calc
      _ ≤ ENNReal.ofReal (((t / 2) ^ q)⁻¹) *
          ∫⁻ y, ENNReal.ofReal (‖T u y‖ ^ q) ∂ν :=
        glyz_measure_tail_le_power ν (hm u hu) hq (by positivity)
      _ ≤ ENNReal.ofReal (((t / 2) ^ q)⁻¹) *
          (ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ q) ∂μ) :=
        mul_le_mul_right hb _
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [Real.div_rpow ht.le (by norm_num), inv_div]
        ring
  have hgq := e2_high_truncation_integrable_power hfm hq₀ hqp
    (div_pos ht hB) hfp
  have hhq := e2_low_truncation_integrable_power hfm (hq₀.trans hqp) hpq
    (div_pos ht hB) hfp
  have he₀ : (fun x => ENNReal.ofReal (‖g x‖ ^ q₀)) =
      {x | t ≤ B * ‖f x‖}.indicator (fun x => ENNReal.ofReal (‖f x‖ ^ q₀)) := by
    funext x
    have he : x ∈ S ↔ t ≤ B * ‖f x‖ := by
      change t / B ≤ ‖f x‖ ↔ _
      rw [div_le_iff₀ hB, mul_comm (‖f x‖)]
    by_cases hx : x ∈ S
    · simp [g, hx, he.mp hx]
    · simp [g, hx, mt he.mpr hx, Real.zero_rpow hq₀.ne']
  have he₁ : (fun x => ENNReal.ofReal (‖h x‖ ^ q₁)) =
      {x | B * ‖f x‖ < t}.indicator (fun x => ENNReal.ofReal (‖f x‖ ^ q₁)) := by
    funext x
    have he : x ∈ S ↔ t ≤ B * ‖f x‖ := by
      change t / B ≤ ‖f x‖ ↔ _
      rw [div_le_iff₀ hB, mul_comm (‖f x‖)]
    by_cases hx : x ∈ S
    · simp [h, hx, not_lt.mpr (he.mp hx), Real.zero_rpow (hq₀.trans (hqp.trans hpq)).ne']
    · simp [h, hx, lt_of_not_ge (mt he.mpr hx)]
  calc
    _ ≤ ν ({y | t / 2 ≤ ‖T g y‖} ∪ {y | t / 2 ≤ ‖T h y‖}) := measure_mono hsplit
    _ ≤ ν {y | t / 2 ≤ ‖T g y‖} + ν {y | t / 2 ≤ ‖T h y‖} := measure_union_le _ _
    _ ≤ _ := by
      have hb₀ := hbound g hgi q₀ A₀ hq₀ hA₀ (hlo g hgi hgq)
      have hb₁ := hbound h hhi' q₁ A₁ (hq₀.trans (hqp.trans hpq)) hA₁ (hhi h hhi' hhq)
      rw [he₀] at hb₀
      rw [he₁] at hb₁
      exact add_le_add hb₀ hb₁

end PlanarNikodym
