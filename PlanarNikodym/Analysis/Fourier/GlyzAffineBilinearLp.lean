import PlanarNikodym.Analysis.Fourier.GlyzAffineLpTransfer
import PlanarNikodym.Analysis.Fourier.GlyzBilinearLp

/-! The common Jacobian factor in a bilinear product is exactly the
square of the factor in the individual Lp norms. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace PlanarNikodym
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem eLpNorm_comp_glyzAdjointEquiv_measurable (L : E ≃L[ℝ] E)
    (f : E → ℂ) (p : ℝ≥0∞) (hf : AEStronglyMeasurable f (Measure.map (glyzAdjointEquiv L) volume)) :
    eLpNorm (f ∘ glyzAdjointEquiv L) p volume =
      ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| ^ (1 / p.toReal) *
        eLpNorm f p volume := by
  have hm : Measure.map (glyzAdjointEquiv L) volume =
      ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| • volume := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E)
      (LinearEquiv.isUnit_det' (glyzAdjointEquiv L).toLinearEquiv).ne_zero
    change Measure.map (glyzAdjointEquiv L) volume =
      ENNReal.ofReal |(LinearMap.det (glyzAdjointEquiv L).toLinearMap)⁻¹| • volume at h
    rwa [det_glyzAdjointEquiv] at h
  rw [← eLpNorm_map_measure hf (glyzAdjointEquiv L).continuous.measurable.aemeasurable, hm]
  simpa only [one_div, ENNReal.toReal_inv, smul_eq_mul] using eLpNorm_smul_measure_of_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero
      (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero))) _ _ _

theorem glyzBilinearLp_frequencyAffine (L : E ≃L[ℝ] E) (a : E)
    (p : ℝ≥0) (hp : 0 < p) (f g : SchwartzMap E ℂ) :
    glyzBilinearLp p (glyzSchwartzFrequencyAffine L a f) (glyzSchwartzFrequencyAffine L a g) =
      glyzAffineLpFactor L p ^ (2 : ℕ) * glyzBilinearLp p f g := by
  let d := |LinearMap.det L.toLinearMap|
  have hd : 0 ≤ d := abs_nonneg _
  have he : eLpNorm (fun x => glyzSchwartzFrequencyAffine L a f x *
      star (glyzSchwartzFrequencyAffine L a g x)) (p / 2 : ℝ≥0) volume =
      ENNReal.ofReal (d ^ (2 : ℕ)) *
        (ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| ^
          (1 / ((p / 2 : ℝ≥0) : ℝ≥0∞).toReal) *
            eLpNorm (fun x => f x * star (g x)) (p / 2 : ℝ≥0) volume) := by
    calc
      _ = eLpNorm ((d ^ (2 : ℕ)) • ((fun x => f x * star (g x)) ∘ glyzAdjointEquiv L))
          (p / 2 : ℝ≥0) volume :=
        eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by
          simp only [norm_mul, norm_star, norm_glyzSchwartzFrequencyAffine,
            Pi.smul_apply, Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg d)]
          dsimp only [d]
          ring)
      _ = _ := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg d),
          eLpNorm_comp_glyzAdjointEquiv_measurable L _ _]
        exact (f.continuous.mul g.continuous.star).aestronglyMeasurable
  have ht := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg d),
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _),
    toReal_eLpNorm (memLp_glyz_pair p hp
      (glyzSchwartzFrequencyAffine L a f) (glyzSchwartzFrequencyAffine L a g)).aestronglyMeasurable,
    toReal_eLpNorm (memLp_glyz_pair p hp f g).aestronglyMeasurable] at ht
  unfold glyzBilinearLp
  rw [ht]
  have hpow : 1 / ((p / 2 : ℝ≥0) : ℝ≥0∞).toReal = (1 / (p : ℝ≥0∞).toReal) * 2 := by
    simp only [ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_ofNat]
    ring
  rw [hpow, Real.rpow_mul (abs_nonneg _), Real.rpow_two]
  unfold glyzAffineLpFactor
  dsimp only [d]
  ring

theorem glyzBilinearLp_symm (p : ℝ≥0) (hp : 0 < p) (f g : SchwartzMap E ℂ) :
    glyzBilinearLp p f g = glyzBilinearLp p g f := by
  unfold glyzBilinearLp
  rw [← toReal_eLpNorm (memLp_glyz_pair p hp f g).aestronglyMeasurable,
    ← toReal_eLpNorm (memLp_glyz_pair p hp g f).aestronglyMeasurable]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall fun x => by simp [mul_comm]

end PlanarNikodym
