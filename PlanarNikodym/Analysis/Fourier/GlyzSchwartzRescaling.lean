import PlanarNikodym.Analysis.Fourier.GlyzFourierAffine
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Actual affine transport of Schwartz Fourier pieces, including exact
support transport and the determinant factor in every Lp seminorm. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform
open scoped FourierTransform ENNReal NNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzSchwartzFrequencyAffine (L : E ≃L[ℝ] E) (a : E) (f : SchwartzMap E ℂ) :
    SchwartzMap E ℂ :=
  𝓕⁻ (((𝓕 f : SchwartzMap E ℂ).compCLMOfContinuousLinearEquiv ℂ L.symm).compSubConstCLM ℂ a)

theorem fourier_glyzSchwartzFrequencyAffine (L : E ≃L[ℝ] E) (a : E)
    (f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (glyzSchwartzFrequencyAffine L a f : E → ℂ) ξ =
      𝓕 (f : E → ℂ) (L.symm (ξ - a)) := by
  change 𝓕 (𝓕⁻ (_ : SchwartzMap E ℂ)) ξ = _
  rw [fourier_fourierInv_eq]
  rfl

theorem glyzSchwartzFrequencyAffine_apply (L : E ≃L[ℝ] E) (a : E)
    (f : SchwartzMap E ℂ) (x : E) :
    glyzSchwartzFrequencyAffine L a f x = (Real.fourierChar (inner ℝ x a) : ℂ) *
      (|LinearMap.det L.toLinearMap| • f (glyzAdjointEquiv L x)) := by
  change (𝓕⁻ (_ : SchwartzMap E ℂ)) x = _
  rw [SchwartzMap.fourierInv_coe]
  have he : ((((𝓕 f : SchwartzMap E ℂ).compCLMOfContinuousLinearEquiv ℂ L.symm).compSubConstCLM ℂ a) : E → ℂ) =
      fun ξ => 𝓕 (f : E → ℂ) (L.symm (ξ - a)) := rfl
  rw [he, glyz_fourierInv_affine,
    f.continuous.fourierInv_fourier_eq f.integrable (𝓕 f : SchwartzMap E ℂ).integrable]

theorem support_fourier_glyzSchwartzFrequencyAffine (L : E ≃L[ℝ] E) (a : E)
    (f : SchwartzMap E ℂ) :
    Function.support (𝓕 (glyzSchwartzFrequencyAffine L a f : E → ℂ)) =
      (fun ξ => a + L ξ) '' Function.support (𝓕 (f : E → ℂ)) := by
  ext ξ
  simp only [Function.mem_support, fourier_glyzSchwartzFrequencyAffine, mem_image]
  constructor
  · intro h
    exact ⟨L.symm (ξ - a), h, by simp [add_comm a]⟩
  · rintro ⟨η, hη, rfl⟩
    simpa using hη

theorem norm_glyzSchwartzFrequencyAffine (L : E ≃L[ℝ] E) (a : E)
    (f : SchwartzMap E ℂ) (x : E) :
    ‖glyzSchwartzFrequencyAffine L a f x‖ =
      |LinearMap.det L.toLinearMap| * ‖f (glyzAdjointEquiv L x)‖ := by
  rw [glyzSchwartzFrequencyAffine_apply, norm_mul, Circle.norm_coe, one_mul,
    norm_smul, Real.norm_eq_abs, abs_abs]

theorem eLpNorm_comp_glyzAdjointEquiv (L : E ≃L[ℝ] E) (f : SchwartzMap E ℂ) (p : ℝ≥0∞) :
    eLpNorm ((f : E → ℂ) ∘ glyzAdjointEquiv L) p volume =
      ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| ^ (1 / p.toReal) *
        eLpNorm (f : E → ℂ) p volume := by
  have hm : Measure.map (glyzAdjointEquiv L) volume =
      ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| • volume := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
      (LinearEquiv.isUnit_det' (glyzAdjointEquiv L).toLinearEquiv).ne_zero
    change Measure.map (glyzAdjointEquiv L) volume =
      ENNReal.ofReal |(LinearMap.det (glyzAdjointEquiv L).toLinearMap)⁻¹| • volume at h
    rwa [det_glyzAdjointEquiv] at h
  rw [← eLpNorm_map_measure f.continuous.aestronglyMeasurable
    (glyzAdjointEquiv L).continuous.measurable.aemeasurable, hm]
  simpa only [one_div, ENNReal.toReal_inv, smul_eq_mul] using eLpNorm_smul_measure_of_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero
      (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero))) _ _ _

theorem eLpNorm_glyzSchwartzFrequencyAffine (L : E ≃L[ℝ] E) (a : E)
    (f : SchwartzMap E ℂ) (p : ℝ≥0∞) :
    eLpNorm (glyzSchwartzFrequencyAffine L a f : E → ℂ) p volume =
      ENNReal.ofReal |LinearMap.det L.toLinearMap| *
        (ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| ^ (1 / p.toReal) *
          eLpNorm (f : E → ℂ) p volume) := by
  calc
    _ = eLpNorm (|LinearMap.det L.toLinearMap| • ((f : E → ℂ) ∘ glyzAdjointEquiv L)) p volume :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by
        simpa only [Pi.smul_apply, Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_abs] using
          norm_glyzSchwartzFrequencyAffine L a f x)
    _ = _ := by rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_abs,
      eLpNorm_comp_glyzAdjointEquiv]

end PlanarNikodym
