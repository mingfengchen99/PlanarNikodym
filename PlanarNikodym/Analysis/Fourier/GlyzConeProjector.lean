import PlanarNikodym.Analysis.Fourier.GlyzConeRadialPartition
import PlanarNikodym.Analysis.Fourier.GlyzAffineBoxInterpolation

/-! Smooth cone projections with positive radial support. A fixed compact
cutoff in normalized conic coordinates is transported by the actual
linear conic frame. Kernel mass is independent of that frame. -/
noncomputable section
open Set Metric MeasureTheory
open scoped FourierTransform NNReal ENNReal BigOperators
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzLinearCutoff (L : E ≃L[ℝ] E) (χ : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm χ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem glyzLinearCutoff_apply (L : E ≃L[ℝ] E) (χ : SchwartzMap E ℂ) (x : E) :
    glyzLinearCutoff L χ x = χ (L.symm x) := rfl

theorem norm_glyzLinearCutoffKernel (L : E ≃L[ℝ] E) (χ : SchwartzMap E ℂ) (x : E) :
    ‖glyzReproducingKernel (glyzLinearCutoff L χ) x‖ =
      |LinearMap.det L.toLinearMap| * ‖glyzReproducingKernel χ (glyzAdjointEquiv L x)‖ := by
  have he := congrArg norm (glyz_fourierInv_affine L 0 (χ : E → ℂ) x)
  simpa only [glyzReproducingKernel, SchwartzMap.fourierInv_coe, sub_zero,
    glyzLinearCutoff, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    norm_mul, Circle.norm_coe, one_mul, norm_smul, Real.norm_eq_abs, abs_abs, Function.comp_def] using he

theorem integral_norm_glyzLinearCutoffKernel (L : E ≃L[ℝ] E) (χ : SchwartzMap E ℂ) :
    (∫ x, ‖glyzReproducingKernel (glyzLinearCutoff L χ) x‖) =
      ∫ x, ‖glyzReproducingKernel χ x‖ := by
  simp_rw [norm_glyzLinearCutoffKernel]
  rw [integral_const_mul, glyz_integral_comp_linearEquiv (glyzAdjointEquiv L)
      (fun y : E => ‖glyzReproducingKernel χ y‖), smul_eq_mul,
    det_glyzAdjointEquiv, ← mul_assoc, ← abs_mul,
    mul_inv_cancel₀ (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero, abs_one, one_mul]

theorem exists_glyz_positive_radial_cutoff (k : ℕ) (H : ℝ)
    {rmin rmax : ℝ} (hrmin : 0 < rmin) :
    ∃ χ : SchwartzMap (GlyzConeSpace k) ℂ,
      (∀ z ∈ glyzConeFrequencyRange k H rmin rmax, χ z = 1) ∧
      (∀ z ∈ Function.support χ,
        ‖(WithLp.ofLp z).1‖ < H + 1 ∧ rmin / 2 < (WithLp.ofLp z).2 ∧
          (WithLp.ofLp z).2 < rmax + 1) := by
  let U : Set (GlyzConeSpace k) := {z | ‖(WithLp.ofLp z).1‖ < H + 1 ∧
    rmin / 2 < (WithLp.ofLp z).2 ∧ (WithLp.ofLp z).2 < rmax + 1}
  have hc := (WithLp.prodContinuousLinearEquiv 2 ℝ (GlyzSpace k) ℝ).continuous
  have hU : IsOpen U := (isOpen_lt (continuous_fst.comp hc).norm continuous_const).inter
    ((isOpen_lt continuous_const (continuous_snd.comp hc)).inter
      (isOpen_lt (continuous_snd.comp hc) continuous_const))
  have hKU : glyzConeFrequencyRange k H rmin rmax ⊆ U := by
    rintro z ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
    have hu' : ‖u‖ ≤ H := by simpa only [mem_closedBall, dist_zero_right] using hu
    change ‖u‖ < H + 1 ∧ rmin / 2 < r ∧ r < rmax + 1
    exact ⟨by linarith, by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨ψ, V, hψ, hcψ, _hr, _hV, hKV, hVψ, hsψ⟩ :=
    exists_compact_smooth_cutoff (isCompact_glyzConeFrequencyRange k H rmin rmax) hU hKU
  let χ : SchwartzMap (GlyzConeSpace k) ℂ :=
    (hcψ.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hψ)
  refine ⟨χ, fun z hz => ?_, fun z hz => ?_⟩
  · change (ψ z : ℂ) = 1
    rw [hVψ z (hKV hz), Complex.ofReal_one]
  · apply hsψ
    apply subset_tsupport
    intro he
    apply hz
    change (ψ z : ℂ) = 0
    rw [he, Complex.ofReal_zero]

/-- Actual uniform cone cutoffs. Their support is a larger cone with
radial interval bounded away from zero, regardless of the jet frame. -/
theorem exists_glyz_cone_cutoffs (k : ℕ) {Q rmin rmax : ℝ}
    (hQ : 0 < Q) (hrmin : 0 < rmin) :
    ∃ Q' M : ℝ, 0 < Q' ∧ 0 < M ∧
      ∀ (γ : ℝ → GlyzSpace k) (s δ : ℝ) (_hδ : 0 < δ)
      (L : GlyzSpace k ≃L[ℝ] GlyzSpace k),
      L.toContinuousLinearMap = glyzCurveJetOperator γ s →
      ∃ χ : SchwartzMap (GlyzConeSpace k) ℂ,
        (∀ z ∈ glyzConeBox k γ s δ Q rmin rmax, χ z = 1) ∧
        Function.support χ ⊆ glyzConeBox k γ s δ Q' (rmin / 2) (rmax + 1) ∧
        (∫ x, ‖glyzReproducingKernel χ x‖) ≤ M := by
  let H := |rmax| * glyzBoxCutoffRadius k Q + 1
  have hH : 0 < H := by dsimp [H]; have := glyzBoxCutoffRadius_pos k hQ; positivity
  obtain ⟨ψ, hψone, hψsupp⟩ := exists_glyz_positive_radial_cutoff k H hrmin (rmax := rmax)
  let Q' := (‖(EuclideanSpace.equiv (Fin k) ℝ).toContinuousLinearMap‖ + 1) * (H + 1) * (2 / rmin)
  have hQ' : 0 < Q' := by dsimp [Q']; positivity
  let M := (∫ x, ‖glyzReproducingKernel ψ x‖) + 1
  have hM : 0 < M := by
    have : (0 : ℝ) ≤ ∫ x, ‖glyzReproducingKernel ψ x‖ := integral_nonneg (fun x => norm_nonneg _)
    dsimp [M]; linarith
  refine ⟨Q', M, hQ', hM, fun γ s δ hδ L hL => ?_⟩
  let P := glyzScaledFrame L δ hδ
  let T := glyzConicEquiv P (γ s)
  refine ⟨glyzLinearCutoff T ψ, ?_, ?_, ?_⟩
  · rintro z ⟨r, hr, ξ, hξ, rfl⟩
    apply hψone
    change WithLp.toLp 2 (P.symm (r • ξ - r • γ s), r) ∈
      glyzConeFrequencyRange k H rmin rmax
    refine ⟨(r • P.symm (ξ - γ s), r), ⟨?_, hr⟩, ?_⟩
    · have hξ' : ξ ∈ glyzFrequencyBox P (γ s) Q := by
        rwa [glyzEnlargedCurveBox_eq_frequencyBox γ s δ Q hδ hQ.le L hL] at hξ
      have hnorm := glyzFrequencyBox_subset_ball P (γ s) hQ hξ'
      simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (hrmin.le.trans hr.1)]
      change r * ‖P.symm (ξ - γ s)‖ ≤ H
      have hrmax : r ≤ |rmax| := hr.2.trans (le_abs_self _)
      exact (mul_le_mul hrmax hnorm (norm_nonneg _) (abs_nonneg _)).trans (by dsimp [H, glyzBoxCutoffRadius]; linarith)
    · congr 1
      simp only [← smul_sub, map_smul]
  · intro z hz
    have hz' : T.symm z ∈ Function.support ψ := hz
    obtain ⟨hu, hrlo, hrhi⟩ := hψsupp _ hz'
    let u := (WithLp.ofLp (T.symm z)).1
    let r := (WithLp.ofLp (T.symm z)).2
    have hr0 : 0 < r := by change 0 < (WithLp.ofLp (T.symm z)).2; linarith
    have hrepr : z = WithLp.toLp 2 (P u + r • γ s, r) := by
      change z = T (WithLp.toLp 2 (u, r))
      simp only [u, r, Prod.mk.eta, WithLp.toLp_ofLp, ContinuousLinearEquiv.apply_symm_apply]
    refine ⟨r, ⟨hrlo.le, hrhi.le⟩, γ s + P (r⁻¹ • u), ?_, ?_⟩
    · rw [glyzEnlargedCurveBox_eq_frequencyBox γ s δ Q' hδ hQ'.le L hL]
      change ‖(EuclideanSpace.equiv (Fin k) ℝ) (P.symm (γ s + P (r⁻¹ • u) - γ s))‖ ≤ Q'
      rw [add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply, map_smul, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
      have he : ‖(EuclideanSpace.equiv (Fin k) ℝ) u‖ ≤
          (‖(EuclideanSpace.equiv (Fin k) ℝ).toContinuousLinearMap‖ + 1) * (H + 1) :=
        ((EuclideanSpace.equiv (Fin k) ℝ).toContinuousLinearMap.le_opNorm u).trans
          (mul_le_mul (by linarith) hu.le (norm_nonneg _) (by positivity))
      have hri : r⁻¹ ≤ 2 / rmin := by
        have hi := (inv_le_inv₀ hr0 (show 0 < rmin / 2 by positivity)).mpr hrlo.le
        simpa only [inv_div] using hi
      calc
        _ ≤ (2 / rmin) * ((‖(EuclideanSpace.equiv (Fin k) ℝ).toContinuousLinearMap‖ + 1) * (H + 1)) :=
          mul_le_mul hri he (norm_nonneg _) (by positivity)
        _ = Q' := by dsimp [Q']; ring
    · rw [hrepr]
      apply congrArg (WithLp.toLp 2)
      apply Prod.ext
      · dsimp only
        rw [smul_add, map_smul, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_comm]
      · rfl
  · rw [integral_norm_glyzLinearCutoffKernel]
    change (∫ x, ‖glyzReproducingKernel ψ x‖) ≤ _ + 1
    linarith

end PlanarNikodym
