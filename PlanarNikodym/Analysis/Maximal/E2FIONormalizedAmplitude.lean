import PlanarNikodym.Analysis.Maximal.E2FIONormalizedDifference
import PlanarNikodym.Analysis.Localization.AnalyticCutoff

/-! Actual jointly smooth compact Gram amplitudes in normalized
difference coordinates. Direction and distance cutoffs are constructed
from the original amplitude support, and the original Gram kernel is
recovered exactly at every pair of distinct input points. -/
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff ComplexConjugate
set_option autoImplicit false
namespace PlanarNikodym
variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

def e2FIONormalizedGramAmplitude (a : Q × Plane → ℂ)
    (χ : Plane → ℝ) (ψ : ℝ → ℝ) (z : ((Q × Plane) × Plane) × ℝ) : ℂ :=
  conj (a z.1.1) * a (z.1.1.1, z.1.1.2 + z.2 • z.1.2) * χ z.1.2 * ψ z.2

theorem e2FIONormalizedGramAmplitude_contDiff {a : Q × Plane → ℂ}
    {χ : Plane → ℝ} {ψ : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (e2FIONormalizedGramAmplitude a χ ψ) := by
  exact ((((Complex.conjCLE.contDiff.comp (ha.comp contDiff_fst.fst)).mul
    (ha.comp (contDiff_fst.fst.fst.prodMk
      (contDiff_fst.fst.snd.add (contDiff_snd.smul contDiff_fst.snd))))).mul
    (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_fst.snd))).mul
    (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_snd)))

omit [NormedSpace ℝ Q] in
theorem e2FIONormalizedGramAmplitude_hasCompactSupport {a : Q × Plane → ℂ}
    {χ : Plane → ℝ} {ψ : ℝ → ℝ} (ha : HasCompactSupport a)
    (hχ : HasCompactSupport χ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (e2FIONormalizedGramAmplitude a χ ψ) := by
  apply HasCompactSupport.intro ((ha.isCompact.prod hχ.isCompact).prod hψ.isCompact)
  intro z hz
  by_cases h1 : a z.1.1 = 0
  · simp [e2FIONormalizedGramAmplitude, h1]
  by_cases h2 : χ z.1.2 = 0
  · simp [e2FIONormalizedGramAmplitude, h2]
  by_cases h3 : ψ z.2 = 0
  · simp [e2FIONormalizedGramAmplitude, h3]
  exact False.elim (hz ⟨⟨subset_tsupport a h1, subset_tsupport χ h2⟩, subset_tsupport ψ h3⟩)

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem e2FIONormalizedGramAmplitude_eq {a : Q × Plane → ℂ}
    {χ : Plane → ℝ} {ψ : ℝ → ℝ} (q : Q) (x y vdir : Plane) (h : ℝ)
    (he : y = x + h • vdir) (hχ : χ vdir = 1) (hψ : ψ h = 1) :
    e2FIONormalizedGramAmplitude a χ ψ (((q,x),vdir),h) =
      conj (a (q,x)) * a (q,y) := by
  simp [e2FIONormalizedGramAmplitude, he, hχ, hψ]

omit [NormedSpace ℝ Q] in
theorem e2_exists_normalized_gram_cutoffs {a : Q × Plane → ℂ}
    (ha : HasCompactSupport a) :
    ∃ (R : ℝ) (χ : Plane → ℝ) (ψ : ℝ → ℝ), 0 < R ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ vdir : Plane, ‖vdir‖ = 1 → χ vdir = 1) ∧
      (∀ vdir ∈ tsupport χ, (1/2 : ℝ) < ‖vdir‖ ∧ ‖vdir‖ < 2) ∧
      (∀ h ∈ Icc (0 : ℝ) (2*R), ψ h = 1) ∧
      (∀ (q : Q) (x y : Plane), (q,x) ∈ tsupport a → (q,y) ∈ tsupport a →
        ‖y-x‖ ≤ 2*R) := by
  obtain ⟨R, hR, hb⟩ := Bornology.IsBounded.exists_pos_norm_le (E := Plane)
    (ha.isCompact.image continuous_snd).isBounded
  obtain ⟨χ, U, hχ, hcχ, _, _, hKU, hUχ, hsχ⟩ := exists_compact_smooth_cutoff
    (isCompact_sphere (0 : Plane) 1)
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
    (show Metric.sphere (0 : Plane) 1 ⊆ {vdir : Plane | (1/2 : ℝ) < ‖vdir‖} ∩
        {vdir : Plane | ‖vdir‖ < 2} from by
      intro vdir hv
      have he : ‖vdir‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
      simp only [mem_inter_iff, mem_setOf_eq, he]
      norm_num)
  obtain ⟨ψ, V, hψ, hcψ, _, _, hKV, hVψ, _⟩ := exists_compact_smooth_cutoff
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2*R))) isOpen_univ (subset_univ _)
  refine ⟨R, χ, ψ, hR, hχ, hcχ, hψ, hcψ, ?_, ?_, ?_, ?_⟩
  · intro vdir hv
    exact hUχ vdir (hKU (by simpa only [Metric.mem_sphere, dist_zero_right] using hv))
  · intro vdir hv
    exact hsχ hv
  · intro h hh
    exact hVψ h (hKV hh)
  · intro q x y hx hy
    calc
      ‖y-x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R+R := add_le_add (hb y ⟨(q,y),hy,rfl⟩) (hb x ⟨(q,x),hx,rfl⟩)
      _ = 2*R := by ring

omit [NormedSpace ℝ Q] in
theorem e2FIONormalizedGramAmplitude_tsupport_subset (a : Q × Plane → ℂ)
    (χ : Plane → ℝ) (ψ : ℝ → ℝ) :
    tsupport (e2FIONormalizedGramAmplitude a χ ψ) ⊆
      {z | z.1.1 ∈ tsupport a ∧
        (z.1.1.1, z.1.1.2 + z.2 • z.1.2) ∈ tsupport a ∧
        z.1.2 ∈ tsupport χ ∧ z.2 ∈ tsupport ψ} := by
  apply closure_minimal
  · intro z hz
    have h1 : a z.1.1 ≠ 0 := by
      intro h
      exact hz (by simp [e2FIONormalizedGramAmplitude, h])
    have h2 : a (z.1.1.1, z.1.1.2 + z.2 • z.1.2) ≠ 0 := by
      intro h
      exact hz (by simp [e2FIONormalizedGramAmplitude, h])
    have h3 : χ z.1.2 ≠ 0 := by
      intro h
      exact hz (by simp [e2FIONormalizedGramAmplitude, h])
    have h4 : ψ z.2 ≠ 0 := by
      intro h
      exact hz (by simp [e2FIONormalizedGramAmplitude, h])
    exact ⟨subset_tsupport a h1, subset_tsupport a h2,
      subset_tsupport χ h3, subset_tsupport ψ h4⟩
  · exact (isClosed_tsupport a |>.preimage continuous_fst.fst).inter
      ((isClosed_tsupport a |>.preimage (continuous_fst.fst.fst.prodMk
        (continuous_fst.fst.snd.add (continuous_snd.smul continuous_fst.snd)))).inter
        ((isClosed_tsupport χ |>.preimage continuous_fst.snd).inter
          (isClosed_tsupport ψ |>.preimage continuous_snd)))

variable [MeasurableSpace Q]

theorem e2_exists_exact_normalized_gram_amplitude
    (μ : Measure Q) {Φ : Q × Plane → ℝ} {a : Q × Plane → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∃ (χ : Plane → ℝ) (ψ : ℝ → ℝ),
      ContDiff ℝ ∞ (e2FIONormalizedGramAmplitude a χ ψ) ∧
      HasCompactSupport (e2FIONormalizedGramAmplitude a χ ψ) ∧
      (∀ z ∈ tsupport (e2FIONormalizedGramAmplitude a χ ψ), (1/2 : ℝ) < ‖z.1.2‖) ∧
      ∀ (r : ℝ) (x y : Plane), x ≠ y →
        e2FIOGramKernel μ r (fun q x => Φ (q,x)) a x y =
          ∫ q, Complex.exp (((r * ‖y-x‖ *
            e2FIONormalizedDifference Φ (((q,x),‖y-x‖⁻¹ • (y-x)),‖y-x‖) : ℝ) : ℂ) *
              Complex.I) *
            e2FIONormalizedGramAmplitude a χ ψ (((q,x),‖y-x‖⁻¹ • (y-x)),‖y-x‖) ∂μ := by
  obtain ⟨R, χ, ψ, _, hχ, hcχ, hψ, hcψ, hχ1, hχs, hψ1, hb⟩ :=
    e2_exists_normalized_gram_cutoffs hc
  refine ⟨χ, ψ, e2FIONormalizedGramAmplitude_contDiff ha hχ hψ,
    e2FIONormalizedGramAmplitude_hasCompactSupport hc hcχ hcψ, ?_, ?_⟩
  · intro z hz
    exact (hχs _ (e2FIONormalizedGramAmplitude_tsupport_subset a χ ψ hz).2.2.1).1
  · intro r x y hxy
    let h : ℝ := ‖y-x‖
    let vdir : Plane := h⁻¹ • (y-x)
    have hp : 0 < h := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    have he : y = x+h • vdir := by
      dsimp only [vdir]
      rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
      abel
    have hv : ‖vdir‖ = 1 := by
      dsimp only [vdir]
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hp]
      exact inv_mul_cancel₀ hp.ne'
    rw [e2FIOGramKernel_phase_difference]
    apply integral_congr_ae
    filter_upwards [] with q
    have hphase : r * (Φ (q,y)-Φ (q,x)) =
        r*h*e2FIONormalizedDifference Φ (((q,x),vdir),h) := by
      have hd := e2FIO_phase_difference_exact hΦ q x vdir h
      rw [← he] at hd
      rw [hd]
      ring
    change Complex.exp (((r * (Φ (q,y)-Φ (q,x)) : ℝ) : ℂ) * Complex.I) *
      (conj (a (q,x))*a (q,y)) =
      Complex.exp (((r*h*e2FIONormalizedDifference Φ (((q,x),vdir),h) : ℝ) : ℂ) * Complex.I) *
        e2FIONormalizedGramAmplitude a χ ψ (((q,x),vdir),h)
    rw [hphase]
    congr 1
    by_cases hax : a (q,x) = 0
    · simp [e2FIONormalizedGramAmplitude, hax]
    by_cases hay : a (q,y) = 0
    · simp [e2FIONormalizedGramAmplitude, ← he, hay]
    have hh : ψ h = 1 := hψ1 h ⟨hp.le, hb q x y (subset_tsupport a hax) (subset_tsupport a hay)⟩
    exact (e2FIONormalizedGramAmplitude_eq q x y vdir h he (hχ1 vdir hv) hh).symm

end PlanarNikodym
