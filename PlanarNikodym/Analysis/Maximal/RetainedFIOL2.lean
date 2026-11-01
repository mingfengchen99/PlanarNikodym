import PlanarNikodym.Analysis.Maximal.RetainedFIOGramDecay
import PlanarNikodym.Analysis.Maximal.E2FIOLocalEnergy

/-! Full retained-parameter FIO L2 estimates with constants before frequency
and input. The entire compact amplitude and original Gram kernel are used. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff ENNReal ComplexConjugate
namespace PlanarNikodym
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [SFinite (volume : Measure V)] [IsFiniteMeasureOnCompacts (volume : Measure V)]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [SFinite (volume : Measure V)] in
theorem exists_retained_uniform_gram_kernel_bound {Φ : (V × Plane) × Plane → ℝ}
    {a : (V × Plane) × Plane → ℂ} (hΦ : Continuous Φ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (x y : Plane),
      ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ ≤ C := by
  obtain ⟨M₀, hM₀⟩ := hc.exists_bound_of_continuous ha
  let M : ℝ := |M₀|+1
  have hM : 0 ≤ M := by positivity
  have hb (z : (V × Plane) × Plane) : ‖a z‖ ≤ M :=
    (hM₀ z).trans (by dsimp [M]; linarith [le_abs_self M₀])
  let K : Set (V × Plane) := Prod.fst '' tsupport a
  have hK : IsCompact K := hc.isCompact.image continuous_fst
  let B : (V × Plane) → ℝ := K.indicator (fun _ => M^2)
  have hB : Integrable B := (integrable_indicator_iff hK.measurableSet).mpr
    (integrableOn_const hK.measure_ne_top)
  refine ⟨∫ q, B q, integral_nonneg (fun q => indicator_nonneg (fun _ _ => sq_nonneg M) q), ?_⟩
  intro r x y
  let F : (V × Plane) → ℂ := fun q =>
    conj (e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q x) *
      e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q y
  have hFx : Continuous (fun q => e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q x) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (hΦ.comp (continuous_id.prodMk continuous_const)))).mul
        continuous_const)).mul (ha.comp (continuous_id.prodMk continuous_const))
  have hFy : Continuous (fun q => e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q y) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (hΦ.comp (continuous_id.prodMk continuous_const)))).mul
        continuous_const)).mul (ha.comp (continuous_id.prodMk continuous_const))
  have hF : Continuous F := (Complex.continuous_conj.comp hFx).mul hFy
  have hFc : HasCompactSupport F := by
    apply HasCompactSupport.intro hK
    intro q hq
    have hz : a (q,x) = 0 := by
      by_contra hn
      exact hq ⟨(q,x),subset_tsupport a hn,rfl⟩
    simp [F,e2FIOAmplitudeKernel,hz]
  have hpoint (q : V × Plane) : ‖F q‖ ≤ B q := by
    by_cases hq : q ∈ K
    · simp only [B,Set.indicator_of_mem hq]
      change ‖conj (e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q x) *
        e2FIOAmplitudeKernel r (fun q x => Φ (q,x)) a q y‖ ≤ _
      rw [norm_mul, RCLike.norm_conj, norm_e2FIOAmplitudeKernel, norm_e2FIOAmplitudeKernel]
      simpa only [pow_two] using mul_le_mul (hb (q,x)) (hb (q,y)) (norm_nonneg _) hM
    · have hz : a (q,x) = 0 := by
        by_contra hn
        exact hq ⟨(q,x),subset_tsupport a hn,rfl⟩
      simp [F,e2FIOAmplitudeKernel,hz,B,hq]
  exact (norm_integral_le_integral_norm F).trans
    (integral_mono (hF.integrable_of_hasCompactSupport hFc).norm hB
      hpoint)

theorem full_fio_energy_of_gram_bound
    {Q : Type*} [NormedAddCommGroup Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    {Φ : Q × Plane → ℝ} {a : Q × Plane → ℂ}
    (hΦ : Continuous Φ) (ha : Continuous a) (hc : HasCompactSupport a)
    (N : ℕ) {r : ℝ} (hr : 0 < r) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x y : Plane,
      ‖e2FIOGramKernel μ r (fun q x => Φ (q,x)) a x y‖ ≤
        C * glyzNormWeight N (r • (y-x)))
    (f : Plane → ℂ) (hf : Continuous f) :
    (∫⁻ q : Q, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ₑ ^ (2 : ℕ) ∂μ) ≤
      (ENNReal.ofReal C * (ENNReal.ofReal ((r^2)⁻¹) *
        ∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight N x))) *
          ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  have he := e2FullFIOIntegral_gram_energy_of_continuous_amplitude μ r
    (fun q x => Φ (q,x)) a f hΦ ha hc hf
  have hel : (∫⁻ q : Q, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ₑ ^ (2 : ℕ) ∂μ) =
      ENNReal.ofReal (∫ q : Q, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ ^ (2 : ℕ) ∂μ) := by
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
  have hrow (x : Plane) : ∫⁻ y : Plane, κ x y = A := by
    change (∫⁻ y : Plane, ENNReal.ofReal C *
      ENNReal.ofReal (glyzNormWeight N (r • (y-x)))) = _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      e2_plane_lintegral_normWeight_smul_sub N hr x]
  have hcol (y : Plane) : ∫⁻ x : Plane, κ x y = A := by
    have hew : (fun x : Plane => κ x y) = fun x : Plane => κ y x := by
      funext x
      simp only [κ,glyzNormWeight,norm_smul,norm_sub_rev]
    rw [hew,hrow]
  rw [hel,he.2]
  calc
    _ ≤ ‖∫ x : Plane, ∫ y : Plane,
        (conj (f x)*f y)*e2FIOGramKernel μ r (fun q x => Φ (q,x)) a x y‖ₑ := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)
    _ ≤ ∫⁻ x : Plane, ‖∫ y : Plane,
        (conj (f x)*f y)*e2FIOGramKernel μ r (fun q x => Φ (q,x)) a x y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x : Plane, ∫⁻ y : Plane,
        ‖(conj (f x)*f y)*e2FIOGramKernel μ r (fun q x => Φ (q,x)) a x y‖ₑ := by
      exact lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x : Plane, ∫⁻ y : Plane, κ x y * (‖f x‖ₑ * ‖f y‖ₑ) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      have hg : ‖e2FIOGramKernel μ r (fun q x => Φ (q,x)) a x y‖ₑ ≤ κ x y := by
        rw [← ofReal_norm]
        change ENNReal.ofReal _ ≤ ENNReal.ofReal C * ENNReal.ofReal _
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd x y)
      simp only [enorm_mul,RCLike.enorm_conj]
      calc
        _ ≤ (‖f x‖ₑ*‖f y‖ₑ)*κ x y := mul_le_mul_right hg _
        _ = _ := mul_comm _ _
    _ ≤ A * ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) :=
      e2_positive_kernel_bilinear_schur volume hκ hf.measurable.enorm A
        (fun x => (hrow x).le) (fun y => (hcol y).le)


theorem exists_retained_gram_polynomial_decay
    {Φ : (V × Plane) × Plane → ℝ} {a : (V × Plane) × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set ((V × Plane) × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (v : V) (q x y : Plane), ((v,q),x) ∈ O → ((v,q),y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,x) -
        e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,y)‖)
    (hsa : tsupport a ⊆ O) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), r ≠ 0 → ∀ (x y : Plane),
      ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ ≤
        C * glyzNormWeight N (r • (y-x)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_retained_uniform_gram_kernel_bound hΦ.continuous ha.continuous hc
  obtain ⟨C, hC, hd⟩ := exists_retained_full_gram_offDiagonal_decay hΦ ha hc hO hcpos hs hsa N
  refine ⟨C₀+C, add_nonneg hC₀ hC, ?_⟩
  intro r hr x y
  by_cases hn : ‖r • (y-x)‖ ≤ 1
  · simpa only [glyzNormWeight, max_eq_left hn, one_pow, inv_one, mul_one] using
      (hb r x y).trans (le_add_of_nonneg_right hC)
  · have hxy : x ≠ y := by
      intro he
      apply hn
      simp [he]
    have hew : (|r * ‖y-x‖|⁻¹)^N = glyzNormWeight N (r • (y-x)) := by
      unfold glyzNormWeight
      rw [max_eq_right (lt_of_not_ge hn).le, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (norm_nonneg (y-x)), inv_pow]
    calc
      _ ≤ C * (|r * ‖y-x‖|⁻¹)^N := hd r hr x y hxy
      _ = C * glyzNormWeight N (r • (y-x)) := by rw [hew]
      _ ≤ (C₀+C) * glyzNormWeight N (r • (y-x)) := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀)
          (glyzNormWeight_pos N _).le


theorem exists_retained_full_fio_energy_bound
    {Φ : (V × Plane) × Plane → ℝ} {a : (V × Plane) × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set ((V × Plane) × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (v : V) (q x y : Plane), ((v,q),x) ∈ O → ((v,q),y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,x) -
        e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,y)‖)
    (hsa : tsupport a ⊆ O) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (r : ℝ), 0 < r → ∀ (f : Plane → ℂ), Continuous f →
      (∫⁻ q : V × Plane, ‖e2FullFIOIntegral r (fun q x => Φ (q,x)) a f q‖ₑ ^ (2 : ℕ)) ≤
        (C * ENNReal.ofReal ((r^2)⁻¹)) * ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  obtain ⟨B, hB, hd⟩ := exists_retained_gram_polynomial_decay hΦ ha hc hO hcpos hs hsa 3
  refine ⟨ENNReal.ofReal B * ∫⁻ x : Plane, ENNReal.ofReal (glyzNormWeight 3 x),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (e2_plane_normWeight_lintegral_ne_top (by norm_num)), ?_⟩
  intro r hr f hf
  have hb := full_fio_energy_of_gram_bound volume hΦ.continuous ha.continuous hc 3 hr hB
    (hd r hr.ne') f hf
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hb


theorem exists_retained_full_fio_L2_bound
    {Φ : (V × Plane) × Plane → ℝ} {a : (V × Plane) × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set ((V × Plane) × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (v : V) (q x y : Plane), ((v,q),x) ∈ O → ((v,q),y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,x) -
        e2FIOParameterGradient e2FIOPlaneDirections
        (fun z : Plane × Plane => Φ ((v,z.1),z.2)) (q,y)‖)
    (hsa : tsupport a ⊆ O) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (r : ℝ), 0 < r → ∀ (f : Plane → ℂ), Continuous f →
      eLpNorm (e2FullFIOIntegral r (fun q x => Φ (q,x)) a f) 2 volume ≤
        C * ENNReal.ofReal r⁻¹ * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hE⟩ := exists_retained_full_fio_energy_bound hΦ ha hc hO hcpos hs hsa
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
