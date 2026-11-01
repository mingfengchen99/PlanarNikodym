import PlanarNikodym.Analysis.Fourier.GlyzFrequencyBoxes

/-! Integrability and exact, frame-independent mass of the actual
volume-normalized polar-box weights. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem integrable_glyzBoxWeight {m A : ℕ} (hA : m < A)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) : Integrable (glyzBoxWeight A L) := by
  let w : GlyzSpace m → ℝ := fun x => glyzDecayWeight A ((EuclideanSpace.equiv (Fin m) ℝ) x)
  have hw : Integrable w := (PiLp.volume_preserving_ofLp (Fin m)).integrable_comp_of_integrable
    (integrable_glyzDecayWeight hA)
  have hmap : Measure.map (glyzAdjointEquiv L) volume =
      ENNReal.ofReal |(LinearMap.det (glyzAdjointEquiv L).toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (LinearEquiv.isUnit_det' (glyzAdjointEquiv L).toLinearEquiv).ne_zero
  have hw' : Integrable w (Measure.map (glyzAdjointEquiv L) volume) := by
    rw [hmap]
    exact hw.smul_measure ENNReal.ofReal_ne_top
  exact (hw'.comp_measurable (glyzAdjointEquiv L).continuous.measurable).const_mul _

theorem integral_glyzBoxWeight (m A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :
    (∫ x, glyzBoxWeight A L x) = ∫ x : Base m, glyzDecayWeight A x := by
  let w : GlyzSpace m → ℝ := fun x => glyzDecayWeight A ((EuclideanSpace.equiv (Fin m) ℝ) x)
  have hp : MeasurePreserving (EuclideanSpace.equiv (Fin m) ℝ)
      (volume : Measure (GlyzSpace m)) (volume : Measure (Base m)) := PiLp.volume_preserving_ofLp (Fin m)
  have hw : (∫ x, w x) = ∫ x : Base m, glyzDecayWeight A x :=
    hp.integral_comp
      (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph.measurableEmbedding (glyzDecayWeight A)
  have hd : LinearMap.det L.toLinearMap ≠ 0 := (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  calc
    _ = |LinearMap.det L.toLinearMap| * ∫ x, w (glyzAdjointEquiv L x) := integral_const_mul _ _
    _ = _ := by
      rw [glyz_integral_comp_linearEquiv (glyzAdjointEquiv L) w,
        det_glyzAdjointEquiv, smul_eq_mul, ← mul_assoc, ← abs_mul,
        mul_inv_cancel₀ hd, abs_one, one_mul, hw]

theorem integrable_glyzPolarWeight {m A : ℕ} (hA : m < A)
    (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) : Integrable (glyzPolarWeight A L) :=
  (integrable_glyzBoxWeight hA L).const_mul _

theorem integral_glyzPolarWeight (m A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m) :
    (∫ x, glyzPolarWeight A L x) = ((2 : ℝ) ^ m)⁻¹ * ∫ x : Base m, glyzDecayWeight A x := by
  unfold glyzPolarWeight
  rw [integral_const_mul, integral_glyzBoxWeight]

theorem glyzPolarWeight_pos {m : ℕ} (A : ℕ) (L : GlyzSpace m ≃L[ℝ] GlyzSpace m)
    (x : GlyzSpace m) : 0 < glyzPolarWeight A L x := by
  unfold glyzPolarWeight glyzBoxWeight
  exact mul_pos (by positivity) (mul_pos
    (abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero) (glyzDecayWeight_pos A _))

end PlanarNikodym
