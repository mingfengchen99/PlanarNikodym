import PlanarNikodym.Analysis.Maximal.E2FIOGramDecay
import PlanarNikodym.Analysis.Maximal.E2FIOPlaneSchurMass
import PlanarNikodym.Analysis.Maximal.E2FIOGramEnergy

/-! The full T*T identity and the actual local Gram decay give
r⁻² square-energy and r⁻¹ L² bounds for the complete two-dimensional
oscillatory integral. Constants precede the frequency and input. This
module proves the local general-phase estimate; it does not identify
the original averaging operator with its partial Fourier transform. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped ENNReal ContDiff ComplexConjugate
set_option autoImplicit false
namespace PlanarNikodym

private theorem e2_scaled_plane_weight_row (N : ℕ) (C : ℝ≥0∞) (r : ℝ) (hr : 0 < r)
    (x : Plane) :
    (∫⁻ y : Plane, C * ENNReal.ofReal (glyzNormWeight N (r • (y-x)))) =
      C * (ENNReal.ofReal ((r^2)⁻¹) * ∫⁻ z : Plane, ENNReal.ofReal (glyzNormWeight N z)) := by
  have hm : Measurable (fun y : Plane => ENNReal.ofReal (glyzNormWeight N (r • (y-x)))) :=
    ENNReal.measurable_ofReal.comp ((continuous_glyzNormWeight N).comp
      (show Continuous (fun y : Plane => r • (y-x)) from
        continuous_const.smul (continuous_id.sub continuous_const))).measurable
  rw [lintegral_const_mul C hm,e2_plane_lintegral_normWeight_smul_sub N hr x]

private theorem e2_scaled_plane_weight_col (N : ℕ) (C : ℝ≥0∞) (r : ℝ) (hr : 0 < r)
    (y : Plane) :
    (∫⁻ x : Plane, C * ENNReal.ofReal (glyzNormWeight N (r • (y-x)))) =
      C * (ENNReal.ofReal ((r^2)⁻¹) * ∫⁻ z : Plane, ENNReal.ofReal (glyzNormWeight N z)) := by
  have hew : (fun x : Plane => C * ENNReal.ofReal (glyzNormWeight N (r • (y-x)))) =
      fun x : Plane => C * ENNReal.ofReal (glyzNormWeight N (r • (x-y))) := by
    funext x
    simp only [glyzNormWeight,norm_smul,norm_sub_rev]
  rw [hew,e2_scaled_plane_weight_row N C r hr y]

theorem e2_full_fio_energy_of_gram_polynomial_bound
    {Φ : Plane × Plane → ℝ} {a : Plane × Plane → ℂ}
    (hΦ : Continuous Φ) (ha : Continuous a) (hc : HasCompactSupport a)
    (N : ℕ) {r : ℝ} (hr : 0 < r) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x y : Plane,
      ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ ≤
        C * glyzNormWeight N (r • (y-x)))
    (f : Plane → ℂ) (hf : Continuous f) :
    (∫⁻ q : Plane, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ₑ ^ (2 : ℕ)) ≤
      (ENNReal.ofReal C * (ENNReal.ofReal ((r^2)⁻¹) *
        ∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight N x))) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  have he := e2FullFIOIntegral_gram_energy_of_continuous_amplitude volume r
    (fun q x => Φ (q,x)) a f hΦ ha hc hf
  have hel : (∫⁻ q : Plane, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (∫ q : Plane, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ ^ (2 : ℕ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal he.1 (Eventually.of_forall fun q => sq_nonneg _)]
    apply lintegral_congr_ae
    filter_upwards [] with q
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  let κ : Plane → Plane → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal C * ENNReal.ofReal (glyzNormWeight N (r • (y-x)))
  let A : ℝ≥0∞ := ENNReal.ofReal C * (ENNReal.ofReal ((r^2)⁻¹) *
    ∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight N x))
  have hW : Measurable (fun z : Plane × Plane =>
      ENNReal.ofReal (glyzNormWeight N (r • (z.2-z.1)))) :=
    ENNReal.measurable_ofReal.comp ((continuous_glyzNormWeight N).comp
      (continuous_const.smul (continuous_snd.sub continuous_fst))).measurable
  have hκ : Measurable (Function.uncurry κ) := measurable_const.mul hW
  have hrow (x : Plane) : ∫⁻ y : Plane, κ x y ≤ A :=
    (e2_scaled_plane_weight_row N (ENNReal.ofReal C) r hr x).le
  have hcol (y : Plane) : ∫⁻ x : Plane, κ x y ≤ A :=
    (e2_scaled_plane_weight_col N (ENNReal.ofReal C) r hr y).le
  rw [hel,he.2]
  calc
    _ ≤ ‖∫ x : Plane, ∫ y : Plane,
        (conj (f x)*f y)*e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)
    _ ≤ ∫⁻ x : Plane, ‖∫ y : Plane,
        (conj (f x)*f y)*e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x : Plane, ∫⁻ y : Plane,
        ‖(conj (f x)*f y)*e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ₑ := by
      exact lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x : Plane, ∫⁻ y : Plane, κ x y * (‖f x‖ₑ * ‖f y‖ₑ) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      have hg : ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ₑ ≤ κ x y := by
        rw [← ofReal_norm]
        change ENNReal.ofReal _ ≤ ENNReal.ofReal C * ENNReal.ofReal _
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd x y)
      simp only [enorm_mul,RCLike.enorm_conj]
      calc
        _ ≤ (‖f x‖ₑ*‖f y‖ₑ)*κ x y := mul_le_mul_right hg _
        _ = _ := mul_comm _ _
    _ ≤ A * ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) :=
      e2_positive_kernel_bilinear_schur volume hκ hf.measurable.enorm A hrow hcol

theorem e2_exists_local_full_fio_energy_bound
    {Φ : Plane × Plane → ℝ} {a : Plane × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set (Plane × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (q : Plane) (x y : Plane), (q,x) ∈ O → (q,y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections Φ (q,x)-
        e2FIOParameterGradient e2FIOPlaneDirections Φ (q,y)‖)
    (hsa : tsupport a ⊆ O) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (r : ℝ), 0 < r → ∀ (f : Plane → ℂ), Continuous f →
      (∫⁻ q : Plane, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ₑ ^ (2 : ℕ)) ≤
        (C * ENNReal.ofReal ((r^2)⁻¹)) * ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨B, hB, hd⟩ := e2_exists_local_gram_polynomial_decay hΦ ha hc hO hcpos hs hsa 3
  refine ⟨ENNReal.ofReal B * ∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight 3 x),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (e2_plane_normWeight_lintegral_ne_top (by norm_num)), ?_⟩
  intro r hr f hf
  have hb := e2_full_fio_energy_of_gram_polynomial_bound hΦ.continuous ha.continuous hc 3 hr hB
    (hd r hr.ne') f hf
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hb

theorem e2_exists_local_full_fio_L2_bound
    {Φ : Plane × Plane → ℝ} {a : Plane × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set (Plane × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (q : Plane) (x y : Plane), (q,x) ∈ O → (q,y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections Φ (q,x)-
        e2FIOParameterGradient e2FIOPlaneDirections Φ (q,y)‖)
    (hsa : tsupport a ⊆ O) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (r : ℝ), 0 < r → ∀ (f : Plane → ℂ), Continuous f →
      eLpNorm (e2FullFIOIntegral r (fun q x => Φ (q,x)) a f) 2 volume ≤
        C * ENNReal.ofReal r⁻¹ * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hE⟩ := e2_exists_local_full_fio_energy_bound hΦ ha hc hO hcpos hs hsa
  refine ⟨C ^ (1/2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC, ?_⟩
  intro r hr f hf
  have hh := ENNReal.rpow_le_rpow (hE r hr f hf) (by norm_num : (0 : ℝ) ≤ 1/2)
  have hscale : ENNReal.ofReal ((r^2)⁻¹) ^ (1/2 : ℝ) = ENNReal.ofReal r⁻¹ := by
    rw [← inv_pow, ENNReal.ofReal_pow (inv_nonneg.mpr hr.le) 2,
      ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hmul (a b : ℝ≥0∞) : (a*b)^(1/2 : ℝ) = a^(1/2 : ℝ)*b^(1/2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg a b (by norm_num)
  simp only [hmul, hscale] at hh
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, ENNReal.rpow_two] using hh

end PlanarNikodym
