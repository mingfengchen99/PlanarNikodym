import PlanarNikodym.Analysis.Maximal.E2FIONormalizedGramKernel
import PlanarNikodym.Analysis.Fourier.GlyzNormWeightMass
import Mathlib.MeasureTheory.Integral.Bochner.Set
/-! The actual full Gram kernel has a uniform diagonal bound and,
on a gradient-separating phase patch, arbitrary polynomial decay.
Both estimates are proved from the compact smooth amplitude. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped ComplexConjugate ContDiff
set_option autoImplicit false
namespace PlanarNikodym

theorem e2_exists_uniform_gram_kernel_bound {Φ : Plane × Plane → ℝ}
    {a : Plane × Plane → ℂ} (hΦ : Continuous Φ) (ha : Continuous a)
    (hc : HasCompactSupport a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (x y : Plane),
      ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ ≤ C := by
  obtain ⟨M₀, hM₀⟩ := hc.exists_bound_of_continuous ha
  let M : ℝ := |M₀|+1
  have hM : 0 ≤ M := by positivity
  have hb (z : Plane × Plane) : ‖a z‖ ≤ M :=
    (hM₀ z).trans (by dsimp [M]; linarith [le_abs_self M₀])
  let K : Set Plane := Prod.fst '' tsupport a
  have hK : IsCompact K := hc.isCompact.image continuous_fst
  let B : Plane → ℝ := K.indicator (fun _ => M^2)
  have hB : Integrable B := (integrable_indicator_iff hK.measurableSet).mpr
    (integrableOn_const hK.measure_ne_top)
  refine ⟨∫ q, B q, integral_nonneg (fun q => indicator_nonneg (fun _ _ => sq_nonneg M) q), ?_⟩
  intro r x y
  let F : Plane → ℂ := fun q =>
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
  have hpoint (q : Plane) : ‖F q‖ ≤ B q := by
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

theorem e2_exists_local_gram_polynomial_decay
    {Φ : Plane × Plane → ℝ} {a : Plane × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {O : Set (Plane × Plane)} (hO : IsOpen O) {c : ℝ} (hcpos : 0 < c)
    (hs : ∀ (q : Plane) (x y : Plane), (q,x) ∈ O → (q,y) ∈ O →
      c * ‖x-y‖ ≤ ‖e2FIOParameterGradient e2FIOPlaneDirections Φ (q,x)-
        e2FIOParameterGradient e2FIOPlaneDirections Φ (q,y)‖)
    (hsa : tsupport a ⊆ O) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), r ≠ 0 → ∀ (x y : Plane),
      ‖e2FIOGramKernel volume r (fun q x => Φ (q,x)) a x y‖ ≤
        C * glyzNormWeight N (r • (y-x)) := by
  obtain ⟨C₀, hC₀, hb⟩ := e2_exists_uniform_gram_kernel_bound hΦ.continuous ha.continuous hc
  obtain ⟨C, hC, hd⟩ := e2_exists_local_gram_offDiagonal_decay hΦ ha hc hO hcpos hs hsa N
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

end PlanarNikodym
