import PlanarNikodym.Analysis.Fourier.LocalizedFrozenFourierTails
import PlanarNikodym.Analysis.Fourier.CompactKernelFourier

/-! The exact frequency representation of a localized variable
extension. Its Fourier coefficients are translated by the actual
gradient of the phase, with the Mathlib `2π` normalization explicit. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def frozenSpatialFrequency (Φ : E × ℝ → ℝ) (w : E) (ρ : ℝ) (y : Plane) : E :=
  (ρ * y.2 / (2 * Real.pi)) •
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun z => Φ (z, y.1)) w)

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_frozenSpatialFrequency {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (w : E) (ρ : ℝ) :
    Continuous (frozenSpatialFrequency Φ w ρ) := by
  have hd : Continuous (fun q : E × ℝ =>
      fderiv ℝ (fun z => Φ (z, q.2)) q.1) :=
    continuous_iff_continuousAt.mpr fun _ =>
      (contDiffAt_fiber_fderiv hΦ.contDiffAt).continuousAt
  exact ((continuous_const.mul continuous_snd).div_const _).smul
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hd.comp (continuous_const.prodMk continuous_fst)))

omit [MeasurableSpace E] [BorelSpace E] in
theorem fourierChar_frozenSpatialFrequency (Φ : E × ℝ → ℝ)
    (w z : E) (ρ : ℝ) (y : Plane) :
    (Real.fourierChar (inner ℝ z (frozenSpatialFrequency Φ w ρ y)) : ℂ) =
      Complex.exp ((((ρ * y.2 * frozenSpatialPhase Φ w z y.1 : ℝ) : ℂ)) * Complex.I) := by
  rw [Real.fourierChar_apply]
  congr 2
  rw [frozenSpatialFrequency, inner_smul_right, real_inner_comm _ z,
    InnerProductSpace.toDual_symm_apply]
  unfold frozenSpatialPhase
  field_simp [Real.pi_ne_zero]

def frozenSpatialData (Φ : E × ℝ → ℝ) (L : ℝ) (w : E)
    (g : Plane → ℂ) (y : Plane) : ℂ :=
  g y * Complex.exp (((L * y.2 * Φ (w, y.1) : ℝ) : ℂ) * Complex.I)

theorem norm_frozenSpatialData {E : Type} (Φ : E × ℝ → ℝ) (L : ℝ) (w : E)
    (g : Plane → ℂ) (y : Plane) : ‖frozenSpatialData Φ L w g y‖ = ‖g y‖ := by
  simp only [frozenSpatialData, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem integrable_frozenSpatialData {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (L : ℝ) (w : E)
    {g : Plane → ℂ} (hg : Integrable g) : Integrable (frozenSpatialData Φ L w g) := by
  have he : Continuous (fun y : Plane =>
      Complex.exp (((L * y.2 * Φ (w, y.1) : ℝ) : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_snd).mul
        (hΦ.continuous.comp (continuous_const.prodMk continuous_fst)))).mul
      continuous_const |>.cexp
  exact hg.mul_bdd (c := 1) he.aestronglyMeasurable
    (ae_of_all _ fun _ => (Complex.norm_exp_ofReal_mul_I _).le)

def localizedFrozenKernel (χ : E → ℂ) (a : E × Plane → ℂ)
    (Φ : E × ℝ → ℝ) (w : E) (α δ : ℝ) (q : E × Plane) : ℂ :=
  localizedFrozenAmplitude χ a Φ (q.1, ((w, q.2), α, δ))

omit [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_localizedFrozenKernel {χ : E → ℂ}
    (hχ : ContDiff ℝ ∞ χ) {a : E × Plane → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : E × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (w : E) (α δ : ℝ) :
    ContDiff ℝ ∞ (localizedFrozenKernel χ a Φ w α δ) :=
  (contDiff_localizedFrozenAmplitude hχ ha hΦ).comp (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_localizedFrozenKernel {χ : E → ℂ}
    (hcχ : HasCompactSupport χ) {a : E × Plane → ℂ} (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (w : E) (α δ : ℝ) :
    HasCompactSupport (localizedFrozenKernel χ a Φ w α δ) := by
  apply HasCompactSupport.intro (hcχ.isCompact.prod (hca.isCompact.image continuous_snd))
  intro q hq
  by_cases hx : q.1 ∈ tsupport χ
  · have hy : q.2 ∉ Prod.snd '' tsupport a := fun h => hq ⟨hx, h⟩
    have ha : a (w + δ • q.1, q.2) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hy ⟨(w + δ • q.1, q.2), h, rfl⟩
    simp [localizedFrozenKernel, localizedFrozenAmplitude, frozenSpatialAmplitude, ha]
  · simp [localizedFrozenKernel, localizedFrozenAmplitude,
      image_eq_zero_of_notMem_tsupport hx]

theorem fourier_const_mul_fun (f : E → ℂ) (c : ℂ) (ξ : E) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem fourier_localizedVariableKernel {Φ : E × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (χ : E → ℂ) (a : E × Plane → ℂ)
    (L δ : ℝ) (w : E) (y : Plane) (ξ : E) :
    𝓕 (fun z => localizedVariableKernel χ a Φ L w δ (z, y)) ξ =
      Complex.exp (((L * y.2 * Φ (w, y.1) : ℝ) : ℂ) * Complex.I) *
      𝓕 (fun z => localizedFrozenKernel χ a Φ w (L * δ ^ 2) δ (z, y))
        (ξ - frozenSpatialFrequency Φ w (L * δ) y) := by
  have he : (fun z => localizedVariableKernel χ a Φ L w δ (z, y)) =
      fun z => Complex.exp (((L * y.2 * Φ (w, y.1) : ℝ) : ℂ) * Complex.I) *
        ((Real.fourierChar (inner ℝ z (frozenSpatialFrequency Φ w (L * δ) y)) : ℂ) *
          localizedFrozenKernel χ a Φ w (L * δ ^ 2) δ (z, y)) := by
    funext z
    rw [localizedVariableKernel_eq_frozen hΦ, fourierChar_frozenSpatialFrequency]
    exact mul_assoc _ _ _
  rw [he, fourier_const_mul_fun, fourier_character_modulation]

theorem fourier_localizedVariableExtensionSchwartz
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a : E × Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (Φ : E × ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (L : ℝ) (w : E) (δ : ℝ) (g : Plane → ℂ) (hg : Integrable g) (ξ : E) :
    𝓕 (localizedVariableExtensionSchwartz χ hχ hcχ a ha hca Φ hΦ L w δ g hg) ξ =
      ∫ y, frozenSpatialData Φ L w g y *
        𝓕 (localizedFrozenAmplitudeSchwartz χ hχ hcχ a ha Φ hΦ ((w, y), L * δ ^ 2, δ))
          (ξ - frozenSpatialFrequency Φ w (L * δ) y) := by
  rw [localizedVariableExtensionSchwartz, fourier_compactKernelIntegralSchwartz]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [fourier_localizedVariableKernel hΦ]
  change g y * (_ * _) = (g y * _) * _
  exact (mul_assoc _ _ _).symm

end PlanarNikodym
