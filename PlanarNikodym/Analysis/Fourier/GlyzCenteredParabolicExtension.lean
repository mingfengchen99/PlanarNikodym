import PlanarNikodym.Analysis.Fourier.GlyzParabolicConeDecoupling
import PlanarNikodym.Analysis.Fourier.GlyzMomentConeCoordinates
import PlanarNikodym.Analysis.Fourier.GlyzParabolicRescaling

/-! Exact identification of the localized cone operator with the
original compact parabolic polynomial extension. Translation of the
output center is absorbed into a unit-modulus factor in the input. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

theorem jetPolynomial_add_coefficients {k : ℕ} (a b : Aux (k + 1)) (t : ℝ) :
    jetPolynomial (a + b) t = jetPolynomial a t + jetPolynomial b t := by
  simp only [jetPolynomial, Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib]

theorem fourierChar_glyzMomentConeFrequency (k : ℕ) (x : GlyzConeSpace k)
    (R : ℝ) (y : Plane) :
    (Real.fourierChar (inner ℝ x
      (glyzCurveConeFrequency k (glyzEuclideanMomentCurve k) (R / (2 * Real.pi)) y)) : ℂ) =
      phaseOscillation (jetPolynomial (glyzMomentConeCoefficientEquiv k x)) (R * y.2) y.1 := by
  rw [Real.fourierChar_apply,
    ← frequency_jetPolynomial_glyzMomentConeCoefficientEquiv]
  unfold phaseOscillation
  congr 2
  field_simp [Real.pi_ne_zero]

def glyzCenteredPolynomialInput {k : ℕ}
    (a : Aux (k + 1)) (R : ℝ) (g : Plane → ℂ) (y : Plane) : ℂ :=
  g y * phaseOscillation (jetPolynomial a) (R * y.2) y.1

@[simp] theorem norm_glyzCenteredPolynomialInput {k : ℕ}
    (a : Aux (k + 1)) (R : ℝ) (g : Plane → ℂ) (y : Plane) :
    ‖glyzCenteredPolynomialInput a R g y‖ = ‖g y‖ := by
  simp only [glyzCenteredPolynomialInput, norm_mul, norm_phaseOscillation, mul_one]

theorem continuous_glyzPolynomialCenterPhase {k : ℕ} (a : Aux (k + 1)) (R : ℝ) :
    Continuous (fun y : Plane => phaseOscillation (jetPolynomial a) (R * y.2) y.1) := by
  have hr : Continuous (fun y : Plane => R * y.2 * jetPolynomial a y.1) := by
    unfold jetPolynomial
    fun_prop
  exact ((Complex.continuous_ofReal.comp hr).mul continuous_const).cexp

theorem aestronglyMeasurable_glyzCenteredPolynomialInput {k : ℕ}
    (a : Aux (k + 1)) (R : ℝ) {g : Plane → ℂ}
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (glyzCenteredPolynomialInput a R g) volume :=
  hg.mul (continuous_glyzPolynomialCenterPhase a R).aestronglyMeasurable

theorem integrable_glyzCenteredPolynomialInput {k : ℕ}
    (a : Aux (k + 1)) (R : ℝ) {g : Plane → ℂ} (hg : Integrable g) :
    Integrable (glyzCenteredPolynomialInput a R g) :=
  hg.mul_bdd (c := 1) (continuous_glyzPolynomialCenterPhase a R).aestronglyMeasurable
    (ae_of_all _ fun _ => (norm_phaseOscillation _ _ _).le)

theorem memLp_glyzCenteredPolynomialInput {k : ℕ}
    (a : Aux (k + 1)) (R : ℝ) {g : Plane → ℂ} {p : ℝ≥0∞} (hg : MemLp g p volume) :
    MemLp (glyzCenteredPolynomialInput a R g) p volume :=
  hg.congr_norm (aestronglyMeasurable_glyzCenteredPolynomialInput a R hg.aestronglyMeasurable)
    (ae_of_all _ fun y => (norm_glyzCenteredPolynomialInput a R g y).symm)

theorem lpNorm_glyzCenteredPolynomialInput {k : ℕ}
    (a : Aux (k + 1)) (R : ℝ) {g : Plane → ℂ}
    (hg : AEStronglyMeasurable g volume) (p : ℝ≥0∞) :
    lpNorm (glyzCenteredPolynomialInput a R g) p volume = lpNorm g p volume := by
  rw [← toReal_eLpNorm (aestronglyMeasurable_glyzCenteredPolynomialInput a R hg),
    ← toReal_eLpNorm hg]
  congr 1
  exact eLpNorm_congr_norm_ae (ae_of_all _ fun y => norm_glyzCenteredPolynomialInput a R g y)

theorem support_glyzCenteredPolynomialInput_subset {k : ℕ}
    (a : Aux (k + 1)) (R : ℝ) (g : Plane → ℂ) :
  Function.support (glyzCenteredPolynomialInput a R g) ⊆ Function.support g :=
  Function.support_mul_subset_left _ _

theorem integrable_polynomialExtension_density {d k : ℕ}
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d k → ℝ) (hH : ContDiff ℝ ∞ H)
    (q : ℝ × Aux (d + 2)) (δ : ℝ) (hδ : δ ≠ 0)
    (α R : ℝ) (w : Aux (k + 1)) {g : Plane → ℂ} (hg : Integrable g) :
    Integrable (fun y : Plane => phaseOscillation (jetPolynomial w) (R * y.2) y.1 *
      glyzCompactParabolicAmplitude A H q δ hδ α w y.1 y.2 * g y) := by
  let S : SchwartzMap (GlyzParabolicSymbolVariables d k) ℂ := hcA.toSchwartzMap hA
  let C := SchwartzMap.seminorm ℝ 0 0 S
  have ha : Continuous (fun y : Plane =>
      glyzCompactParabolicAmplitude A H q δ hδ α w y.1 y.2) := by
    unfold glyzCompactParabolicAmplitude
    have hv : Continuous (fun y : Plane =>
        (((q, (lowerDegreeDilation k δ hδ).symm w), y), δ)) := by fun_prop
    exact (hA.continuous.comp hv).mul
      (((Complex.continuous_ofReal.comp
        (continuous_const.mul (hH.continuous.comp hv))).mul continuous_const).cexp)
  have hm := ((continuous_glyzPolynomialCenterPhase w R).mul ha).aestronglyMeasurable.mul
    hg.aestronglyMeasurable
  apply (hg.norm.const_mul C).mono' hm
  filter_upwards [] with y
  change ‖phaseOscillation (jetPolynomial w) (R * y.2) y.1 *
      glyzCompactParabolicAmplitude A H q δ hδ α w y.1 y.2 * g y‖ ≤ C * ‖g y‖
  simp only [norm_mul, norm_phaseOscillation, one_mul,
    glyzCompactParabolicAmplitude, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact mul_le_mul_of_nonneg_right
    (S.norm_le_seminorm ℝ (((q, (lowerDegreeDilation k δ hδ).symm w), y), δ))
    (norm_nonneg (g y))

/-- The input is only L¹; the passage from the product integral to the
iterated polynomial extension uses an explicitly integrable density. -/
theorem oscillatoryConeExtension_eq_centered_polynomialExtension {d k : ℕ}
    (χ : GlyzConeSpace k → ℂ)
    (A : GlyzParabolicSymbolVariables d k → ℂ)
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (H : GlyzParabolicSymbolVariables d k → ℝ) (hH : ContDiff ℝ ∞ H)
    (p : GlyzLocalizedParabolicParameters d k) (hs : p.scale = 1)
    (α R : ℝ) (g : Plane → ℂ) (hg : Integrable g) (x : GlyzConeSpace k) :
    oscillatoryConeExtension
      (glyzLocalizedParabolicAmplitude χ A (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap p)
      (glyzParabolicSample H (glyzMomentConeCoefficientEquiv k).toContinuousLinearMap p)
      α (glyzCurveConeFrequency k (glyzEuclideanMomentCurve k) (R / (2 * Real.pi)))
      (glyzCenteredPolynomialInput p.center R g) x =
      χ x * polynomialExtension
        (glyzCompactParabolicAmplitude A H p.frozen p.δ p.δ_pos.ne' α)
        g R (p.center + glyzMomentConeCoefficientEquiv k x) := by
  rw [oscillatoryConeExtension_glyzLocalizedParabolicAmplitude]
  congr 1
  let w := p.center + glyzMomentConeCoefficientEquiv k x
  let F : Plane → ℂ := fun y =>
    phaseOscillation (jetPolynomial w) (R * y.2) y.1 *
      glyzCompactParabolicAmplitude A H p.frozen p.δ p.δ_pos.ne' α w y.1 y.2 * g y
  have hi : Integrable F :=
    integrable_polynomialExtension_density A hA hcA H hH p.frozen p.δ p.δ_pos.ne' α R w hg
  calc
    _ = ∫ y, F y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [fourierChar_glyzMomentConeFrequency]
      have he : phaseOscillation (jetPolynomial w) (R * y.2) y.1 =
          phaseOscillation (jetPolynomial p.center) (R * y.2) y.1 *
            phaseOscillation (jetPolynomial (glyzMomentConeCoefficientEquiv k x)) (R * y.2) y.1 := by
        simp only [w, phaseOscillation, jetPolynomial_add_coefficients]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      dsimp only [F]
      rw [he]
      simp only [glyzCenteredPolynomialInput, glyzParabolicSample,
        inverseCoefficientVariables, ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.coe_coe,
        hs, one_smul, glyzCompactParabolicAmplitude, w]
      ring
    _ = _ := integral_prod_symm F hi

end PlanarNikodym
