import PlanarNikodym.Analysis.Fourier.GlyzNormWeightMass
import PlanarNikodym.Analysis.Fourier.GlyzConeArcSupport

/-! Actual scalar changes of the physical variable, including Fourier
support, neighborhood thickness, and local integral Jacobians. -/
noncomputable section
open Set Metric MeasureTheory FourierTransform
open scoped FourierTransform ENNReal Pointwise
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzSchwartzSpatialDilation (b : ℝ) (hb : b ≠ 0) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  |LinearMap.det (glyzScalarEquiv (E := E) b hb).toLinearMap|⁻¹ •
    glyzSchwartzFrequencyAffine (glyzScalarEquiv b hb) 0 f

@[simp] theorem glyzSchwartzSpatialDilation_apply (b : ℝ) (hb : b ≠ 0)
    (f : SchwartzMap E ℂ) (x : E) : glyzSchwartzSpatialDilation b hb f x = f (b • x) := by
  have hd : |LinearMap.det (glyzScalarEquiv (E := E) b hb).toLinearMap| ≠ 0 :=
    abs_ne_zero.mpr (LinearEquiv.isUnit_det' (glyzScalarEquiv (E := E) b hb).toLinearEquiv).ne_zero
  simp [glyzSchwartzSpatialDilation, glyzSchwartzFrequencyAffine_apply, hd]

theorem support_fourier_glyzSchwartzSpatialDilation (b : ℝ) (hb : b ≠ 0)
    (f : SchwartzMap E ℂ) :
    Function.support (𝓕 (glyzSchwartzSpatialDilation b hb f : E → ℂ)) ⊆
      (fun ξ : E => b • ξ) '' Function.support (𝓕 (f : E → ℂ)) := by
  intro ξ hξ
  have hξ' : ξ ∈ Function.support (𝓕
      (glyzSchwartzFrequencyAffine (glyzScalarEquiv b hb) 0 f : E → ℂ)) := by
    intro hz
    apply hξ
    change 𝓕 (_ • glyzSchwartzFrequencyAffine (glyzScalarEquiv b hb) 0 f) ξ = 0
    rw [fourier_smul]
    change (_ : ℝ) • 𝓕 (glyzSchwartzFrequencyAffine (glyzScalarEquiv b hb) 0 f : E → ℂ) ξ = 0
    rw [hz, smul_zero]
  simpa only [support_fourier_glyzSchwartzFrequencyAffine, zero_add, glyzScalarEquiv_apply] using hξ'

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyz_cthickening_subset_add_closedBall {K : Set E} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) : cthickening R K ⊆ K + closedBall (0 : E) R := by
  rw [hK.cthickening_eq_biUnion_closedBall hR]
  rintro x ⟨_, ⟨y, rfl⟩, _, ⟨hy, rfl⟩, hx⟩
  refine ⟨y, hy, x - y, ?_, by abel_nf⟩
  simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hx

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyz_inverse_dilation_neighborhood {K : Set E} (hK : IsCompact K)
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) :
    (fun ξ : E => ρ⁻¹ • ξ) '' cthickening R ((fun ξ : E => ρ • ξ) '' K) ⊆
      K + closedBall (0 : E) (R / ρ) := by
  rintro x ⟨ξ, hξ, rfl⟩
  have hK' : IsCompact ((fun ξ : E => ρ • ξ) '' K) := hK.image (by fun_prop)
  obtain ⟨_, ⟨η, hη, rfl⟩, e, he, rfl⟩ := glyz_cthickening_subset_add_closedBall hK' hR hξ
  refine ⟨η, hη, ρ⁻¹ • e, ?_, ?_⟩
  · have he' : ‖e‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using he
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hρ)]
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left he' (inv_nonneg.mpr hρ.le)
  · simp only [smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

theorem glyzSchwartzSpatialDilation_neighborhood_support
    (f : SchwartzMap E ℂ) {K : Set E} (hK : IsCompact K)
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hf : Function.support (𝓕 (f : E → ℂ)) ⊆
      cthickening R ((fun ξ : E => ρ • ξ) '' K)) :
    Function.support (𝓕 (glyzSchwartzSpatialDilation ρ⁻¹ (inv_ne_zero hρ.ne') f : E → ℂ)) ⊆
      K + closedBall (0 : E) (R / ρ) :=
  (support_fourier_glyzSchwartzSpatialDilation _ _ f).trans
    ((image_mono hf).trans (glyz_inverse_dilation_neighborhood hK hρ hR))

theorem glyz_setLIntegral_comp_smul (F : E → ℝ≥0∞) {b : ℝ} (hb : 0 < b) (R : ℝ) :
    (∫⁻ x in closedBall (0 : E) R, F (b • x)) =
      ENNReal.ofReal ((b ^ Module.finrank ℝ E)⁻¹) *
        ∫⁻ x in closedBall (0 : E) (b * R), F x := by
  classical
  have he (x : E) : b • x ∈ closedBall (0 : E) (b * R) ↔ x ∈ closedBall (0 : E) R := by
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    exact mul_le_mul_iff_right₀ hb
  have hind : (closedBall (0 : E) R).indicator (fun x => F (b • x)) =
      fun x => (closedBall (0 : E) (b * R)).indicator F (b • x) := by
    ext x
    by_cases hx : x ∈ closedBall (0 : E) R
    · simp only [indicator_of_mem hx, indicator_of_mem (he x |>.mpr hx)]
    · simp only [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (he x |>.mp h))]
  rw [← lintegral_indicator measurableSet_closedBall, hind,
    glyz_lintegral_comp_smul _ hb.ne', lintegral_indicator measurableSet_closedBall,
    abs_of_pos (inv_pos.mpr (pow_pos hb _))]

end PlanarNikodym
