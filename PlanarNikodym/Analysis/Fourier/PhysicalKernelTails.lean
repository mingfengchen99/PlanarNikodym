import PlanarNikodym.Analysis.Fourier.PartialExtensionLInfinity
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Physical localization of the genuine frequency multiplier. The input
outside a fixed neighborhood of the averaging curves contributes an
arbitrarily rapidly decreasing Lp error. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym
set_option backward.isDefEq.respectTransparency false

def planeDecayWeight (x : Plane) : ℝ := (1 + ‖x‖) ^ (-(3 : ℝ))

theorem planeDecayWeight_pos (x : Plane) : 0 < planeDecayWeight x := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem continuous_planeDecayWeight : Continuous planeDecayWeight := by
  unfold planeDecayWeight
  exact (continuous_const.add continuous_norm).rpow_const
    (fun x => Or.inl (by positivity : (1 : ℝ) + ‖x‖ ≠ 0))

theorem memLp_planeDecayWeight (p : ℝ≥0∞) (hp : 1 ≤ p) :
    MemLp planeDecayWeight p volume := by
  have hm : AEStronglyMeasurable planeDecayWeight volume :=
    continuous_planeDecayWeight.aestronglyMeasurable
  by_cases ht : p = (∞ : ℝ≥0∞)
  · subst p
    apply memLp_top_of_bound hm 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (planeDecayWeight_pos x)]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [norm_nonneg x]) (by norm_num)
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hpR : 1 ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_mono ht hp)
  apply (integrable_norm_rpow_iff hm hp0 ht).mp
  have hi := integrable_one_add_norm (E := Plane) (μ := volume)
    (show (Module.finrank ℝ Plane : ℝ) < 3 * p.toReal by
      simp only [Plane, Module.finrank_prod, Module.finrank_self, Nat.reduceAdd,
        Nat.cast_ofNat]
      linarith)
  apply hi.congr
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (planeDecayWeight_pos x)]
  dsimp only [planeDecayWeight]
  rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + ‖x‖)]
  congr 1
  ring

theorem schwartz_scaled_kernel_far_bound (K : SchwartzMap Plane ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Plane, 1 ≤ ‖x‖ →
      r ^ 2 * ‖K (r • x)‖ ≤ C * (r⁻¹) ^ N * planeDecayWeight x := by
  obtain ⟨B, hB, hb⟩ := K.decay (N + 5) 0
  simp only [norm_iteratedFDeriv_zero] at hb
  refine ⟨8 * B, by positivity, ?_⟩
  intro r hr x hx
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hx0 : 0 < ‖x‖ := zero_lt_one.trans_le hx
  have hd := hb (r • x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, mul_pow] at hd
  have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ hr
  have hxN : 1 ≤ ‖x‖ ^ (N + 2) := one_le_pow₀ hx
  have hpow : r ^ (N + 2) * ‖x‖ ^ 3 ≤ r ^ (N + 5) * ‖x‖ ^ (N + 5) := by
    calc
      _ ≤ (r ^ (N + 2) * r ^ 3) * (‖x‖ ^ 3 * ‖x‖ ^ (N + 2)) := by
        gcongr
        · exact le_mul_of_one_le_right (by positivity) hr3
        · exact le_mul_of_one_le_right (by positivity) hxN
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; congr 1; omega
  have hd' : r ^ (N + 2) * ‖x‖ ^ 3 * ‖K (r • x)‖ ≤ B :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hd
  have hmain : r ^ 2 * ‖K (r • x)‖ ≤ B * (r⁻¹) ^ N * (‖x‖ ^ 3)⁻¹ := by
    apply (le_div_iff₀ (pow_pos hx0 3)).mpr
    rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hr0 N)).mpr
    simpa only [div_eq_mul_inv, inv_pow] using
      (show (r ^ 2 * ‖K (r • x)‖ * ‖x‖ ^ 3) * r ^ N ≤ B by
        convert hd' using 1; ring)
  have hw : (‖x‖ ^ 3)⁻¹ ≤ 8 * planeDecayWeight x := by
    dsimp only [planeDecayWeight]
    rw [Real.rpow_neg (by positivity)]
    norm_num only [Real.rpow_ofNat]
    apply (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖) ^ 3)).mpr
    rw [mul_comm]
    apply (div_le_iff₀ (pow_pos hx0 3)).mpr
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖)
      (show 1 + ‖x‖ ≤ 2 * ‖x‖ by linarith) 3
    simpa only [mul_pow, show (2 : ℝ) ^ 3 = 8 by norm_num] using h
  exact hmain.trans (by
    calc
      _ ≤ B * (r⁻¹) ^ N * (8 * planeDecayWeight x) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring)

theorem exists_scaledFrequencyConvolution_far_enorm_bound
    {m : Plane → ℝ} (hm : ContDiff ℝ ∞ m) (hc : HasCompactSupport m)
    (p q : ℝ≥0∞) [ENNReal.HolderConjugate q p] (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ f : Plane → ℂ, Integrable f →
      ∀ x : Plane, (∀ y, f y ≠ 0 → 1 ≤ ‖x - y‖) →
      ‖scaledFrequencyConvolution m r f x‖ₑ ≤
        ENNReal.ofReal (C * (r⁻¹) ^ N) * eLpNorm f p volume := by
  let K := inverseFourierSchwartz m hm hc
  obtain ⟨B, hB, hb⟩ := schwartz_scaled_kernel_far_bound K N
  have hw := memLp_planeDecayWeight q (ENNReal.HolderConjugate.one_le q p)
  let V : ℝ := (eLpNorm planeDecayWeight q volume).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨B * V, mul_nonneg hB.le hV, ?_⟩
  intro r hr f hf x hs
  let W : Plane → ℝ := fun y => planeDecayWeight (x - y)
  have hW : AEStronglyMeasurable W volume :=
    (continuous_planeDecayWeight.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hholder : (∫⁻ y, ‖W y‖ₑ * ‖f y‖ₑ) ≤
      eLpNorm W q volume * eLpNorm f p volume := by
    simp_rw [← enorm_smul]
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ) hf.aestronglyMeasurable hW
  have heW : eLpNorm W q volume = ENNReal.ofReal V := by
    rw [show W = planeDecayWeight ∘ (fun y : Plane => x - y) from rfl,
      eLpNorm_comp_measurePreserving hw.aestronglyMeasurable
        (Measure.measurePreserving_sub_left volume x),
      ENNReal.ofReal_toReal hw.eLpNorm_ne_top]
  have hb' (y : Plane) :
      ‖r ^ 2 • (K (r • (x - y)) * f y)‖ₑ ≤
        ENNReal.ofReal (B * (r⁻¹) ^ N) * (‖W y‖ₑ * ‖f y‖ₑ) := by
    by_cases hy : f y = 0
    · simp [hy]
    have h := ENNReal.ofReal_le_ofReal (hb r hr (x - y) (hs y hy))
    rw [ENNReal.ofReal_mul (sq_nonneg r), ofReal_norm,
      ENNReal.ofReal_mul (by positivity : 0 ≤ B * (r⁻¹) ^ N)] at h
    have hw' : ENNReal.ofReal (planeDecayWeight (x - y)) = ‖W y‖ₑ := by
      rw [Real.enorm_eq_ofReal (planeDecayWeight_pos _).le]
    rw [hw'] at h
    rw [enorm_smul, Real.enorm_eq_ofReal (sq_nonneg r), enorm_mul, ← mul_assoc]
    exact (mul_le_mul_left h ‖f y‖ₑ).trans_eq (mul_assoc _ _ _)
  calc
    _ = ‖∫ y, r ^ 2 • (K (r • (x - y)) * f y)‖ₑ := by
      rw [integral_smul]
      simp only [K, inverseFourierSchwartz_apply, scaledFrequencyConvolution]
    _ ≤ ∫⁻ y, ‖r ^ 2 • (K (r • (x - y)) * f y)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal (B * (r⁻¹) ^ N) * (‖W y‖ₑ * ‖f y‖ₑ) :=
      lintegral_mono hb'
    _ = ENNReal.ofReal (B * (r⁻¹) ^ N) * (∫⁻ y, ‖W y‖ₑ * ‖f y‖ₑ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (B * (r⁻¹) ^ N) *
        (eLpNorm W q volume * eLpNorm f p volume) :=
      mul_le_mul_right hholder _
    _ = _ := by
      rw [heW, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end PlanarNikodym
