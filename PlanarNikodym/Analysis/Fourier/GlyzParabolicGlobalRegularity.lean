import PlanarNikodym.Analysis.Fourier.GlyzCenteredParabolicDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzParabolicOutputSupport

/-! The genuine compact parabolic extension is Schwartz in global
Euclidean output coordinates, even for an L¹ input. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

theorem exists_glyz_global_parabolic_schwartz {d k : ℕ}
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d k → ℝ) (hH : ContDiff ℝ ∞ H)
    (q : ℝ × Aux (d + 2)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (α R : ℝ) (g : Plane → ℂ) (hg : Integrable g) :
    ∃ S : SchwartzMap (GlyzConeSpace k) ℂ, ∀ x,
      S x = polynomialExtension (glyzCompactParabolicAmplitude A H q δ hδ.ne' α)
        g R (glyzMomentConeCoefficientEquiv k x) := by
  obtain ⟨L, _, hL⟩ := exists_glyz_compact_parabolic_cone_output_bound A hcA
    (glyzMomentConeCoefficientEquiv k)
  obtain ⟨χ, V, hχ, hcχ, _, _, hBV, hV1, _⟩ :=
    exists_compact_smooth_cutoff (K := closedBall (0 : GlyzConeSpace k) ((δ ^ k)⁻¹ * L))
      (S := univ) (isCompact_closedBall _ _) isOpen_univ (subset_univ _)
  let χc : GlyzConeSpace k → ℂ := fun x => (χ x : ℂ)
  have hχc : ContDiff ℝ ∞ χc := Complex.ofRealCLM.contDiff.comp hχ
  have hcχc : HasCompactSupport χc := hcχ.comp_left (g := Complex.ofRealCLM) rfl
  let u : GlyzLocalizedParabolicParameters d k :=
    ⟨δ, hδ, hδ1, q, 0, 1, by norm_num⟩
  let ga := glyzCenteredPolynomialInput u.center R g
  have hga : Integrable ga := integrable_glyzCenteredPolynomialInput _ R hg
  let S := oscillatoryConeExtensionSchwartz
    (glyzLocalizedParabolicAmplitude χc A (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap u)
    (glyzParabolicSample H (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap u)
    (contDiff_glyzLocalizedParabolicAmplitude hχc hA _ u)
    (contDiff_glyzParabolicSample hH _ u)
    (hasCompactSupport_glyzLocalizedParabolicAmplitude hcχc hcA _ u)
    α (glyzCurveConeFrequency k (glyzEuclideanMomentCurve k) (R / (2 * Real.pi)))
    (contDiff_glyzCurveConeFrequency _ (contDiff_glyzEuclideanMomentCurve k) _) ga hga
  refine ⟨S, fun x => ?_⟩
  change oscillatoryConeExtension _ _ _ _ _ x = _
  rw [oscillatoryConeExtension_eq_centered_polynomialExtension χc A hA hcA H hH u rfl α R g hg]
  simp only [u, zero_add]
  by_cases hx : polynomialExtension (glyzCompactParabolicAmplitude A H q δ hδ.ne' α)
      g R (glyzMomentConeCoefficientEquiv k x) = 0
  · rw [hx, mul_zero]
  · have hχx : χc x = 1 := by
      simp only [χc, hV1 x (hBV (hL H q δ hδ hδ1 α R g hx)), Complex.ofReal_one]
    rw [hχx, one_mul]

theorem continuous_glyz_global_parabolic {d k : ℕ}
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d k → ℝ) (hH : ContDiff ℝ ∞ H)
    (q : ℝ × Aux (d + 2)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (α R : ℝ) (g : Plane → ℂ) (hg : Integrable g) :
    Continuous (fun x => polynomialExtension
      (glyzCompactParabolicAmplitude A H q δ hδ.ne' α) g R
        (glyzMomentConeCoefficientEquiv k x)) := by
  obtain ⟨S, hS⟩ := exists_glyz_global_parabolic_schwartz A hA hcA H hH q hδ hδ1 α R g hg
  exact S.continuous.congr hS

end PlanarNikodym
