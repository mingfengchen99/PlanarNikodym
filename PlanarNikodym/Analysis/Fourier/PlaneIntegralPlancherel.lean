import PlanarNikodym.Analysis.Fourier.FourierIntegralL2
import PlanarNikodym.Analysis.Fourier.BandOscillatoryRepresentation

/-! Actual planar Fourier integrals on L¹∩L², using the original product
Lebesgue measure and transporting only the calculation to Euclidean space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped FourierTransform ENNReal
namespace PlanarNikodym

def planeInverseFourierIntegral (f : Plane → ℂ) (x : Plane) : ℂ :=
  ∫ ξ : Plane, f ξ * planeFourierCharacter x ξ

theorem planeInverseFourierIntegral_eq_euclidean (f : Plane → ℂ) (x : Plane) :
    planeInverseFourierIntegral f x =
      𝓕⁻ (fun ξ : FourierPlane => f (WithLp.ofLp ξ)) (WithLp.toLp 2 x) := by
  rw [Real.fourierInv_eq']
  unfold planeInverseFourierIntegral
  rw [← (WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 Plane).symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial,
    smul_eq_mul, planeFourierCharacter, fourierPhase]
  rw [mul_comm]

theorem continuous_planeInverseFourierIntegral {f : Plane → ℂ} (h1 : Integrable f) :
    Continuous (planeInverseFourierIntegral f) := by
  have h1E : Integrable (fun ξ : FourierPlane => f (WithLp.ofLp ξ)) :=
    (WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_of_integrable h1
  have hcont : Continuous (𝓕⁻ (fun ξ : FourierPlane => f (WithLp.ofLp ξ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂.neg h1E
  have heq : planeInverseFourierIntegral f = fun x : Plane =>
      𝓕⁻ (fun ξ : FourierPlane => f (WithLp.ofLp ξ)) (WithLp.toLp 2 x) :=
    funext (planeInverseFourierIntegral_eq_euclidean f)
  rw [heq]
  exact hcont.comp (fourierPlaneEquiv.symm.continuous)

theorem lintegral_planeInverseFourierIntegral_sq {f : Plane → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫⁻ x : Plane, ‖planeInverseFourierIntegral f x‖ₑ ^ (2 : ℕ)) =
      ∫⁻ ξ : Plane, ‖f ξ‖ₑ ^ (2 : ℕ) := by
  let fE : FourierPlane → ℂ := fun ξ => f (WithLp.ofLp ξ)
  have h1E : Integrable fE :=
    (WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_of_integrable h1
  have h2E : MemLp fE 2 := h2.comp_measurePreserving (WithLp.volume_preserving_ofLp ℝ ℝ)
  calc
    _ = ∫⁻ x : FourierPlane,
        ‖planeInverseFourierIntegral f (WithLp.ofLp x)‖ₑ ^ (2 : ℕ) :=
      ((WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp
        ((continuous_planeInverseFourierIntegral h1).enorm.measurable.pow_const _)).symm
    _ = ∫⁻ x : FourierPlane, ‖𝓕⁻ fE x‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro x
      rw [planeInverseFourierIntegral_eq_euclidean]
    _ = ∫⁻ ξ : FourierPlane, ‖fE ξ‖ₑ ^ (2 : ℕ) := lintegral_fourierInvIntegral_sq h1E h2E
    _ = _ := (WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp_emb
      (MeasurableEquiv.toLp 2 Plane).symm.measurableEmbedding (fun ξ => ‖f ξ‖ₑ ^ (2 : ℕ))

theorem lintegral_scaled_planeInverseFourierIntegral_sq {f : Plane → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : Plane, ‖planeInverseFourierIntegral f (r • x)‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) * ∫⁻ ξ : Plane, ‖f ξ‖ₑ ^ (2 : ℕ) := by
  calc
    _ = ∫⁻ x : Plane, ‖planeInverseFourierIntegral f x‖ₑ ^ (2 : ℕ)
        ∂Measure.map (fun x : Plane => r • x) volume :=
      (lintegral_map ((continuous_planeInverseFourierIntegral h1).enorm.measurable.pow_const _)
        (by fun_prop)).symm
    _ = ENNReal.ofReal (r⁻¹ ^ (2 : ℕ)) *
        ∫⁻ x : Plane, ‖planeInverseFourierIntegral f x‖ₑ ^ (2 : ℕ) := by
      rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure, smul_eq_mul]
      congr 1
      have hd : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
      rw [hd, abs_of_pos (inv_pos.mpr (pow_pos hr 2)), inv_pow]
    _ = _ := by rw [lintegral_planeInverseFourierIntegral_sq h1 h2]

theorem lintegral_planeFourierIntegral_sq_of_integrable {f : Plane → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫⁻ ξ : Plane, ‖planeFourierIntegral f ξ‖ₑ ^ (2 : ℕ)) =
      ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ) := by
  let fE : FourierPlane → ℂ := fun x => f (WithLp.ofLp x)
  have h1E : Integrable fE :=
    (WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_of_integrable h1
  have h2E : MemLp fE 2 := h2.comp_measurePreserving (WithLp.volume_preserving_ofLp ℝ ℝ)
  calc
    _ = ∫⁻ ξ : FourierPlane, ‖planeFourierIntegral f (WithLp.ofLp ξ)‖ₑ ^ (2 : ℕ) :=
      ((WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp
        ((continuous_planeFourierIntegral h1).enorm.measurable.pow_const _)).symm
    _ = ∫⁻ ξ : FourierPlane, ‖𝓕 fE ξ‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro ξ
      rw [planeFourierIntegral_eq_euclidean]
    _ = ∫⁻ x : FourierPlane, ‖fE x‖ₑ ^ (2 : ℕ) := lintegral_fourierIntegral_sq h1E h2E
    _ = _ := (WithLp.volume_preserving_ofLp ℝ ℝ).lintegral_comp_emb
      (MeasurableEquiv.toLp 2 Plane).symm.measurableEmbedding (fun x => ‖f x‖ₑ ^ (2 : ℕ))

end PlanarNikodym
