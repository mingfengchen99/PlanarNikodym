import PlanarNikodym.Analysis.Fourier.GlyzPolarSubspaceWeight
import PlanarNikodym.Analysis.Fourier.GlyzPositiveConvolution

/-! Actual finite, even averaging measures on Euclidean subspaces.
The coordinates are orthonormal, followed by the maximum norm. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

def glyzCoordinateWeight {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l) (A : ℕ) (b : ℝ) (z : H) : ℝ :=
  glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) (e z))

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
theorem continuous_glyzCoordinateWeight {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l) (A : ℕ) (b : ℝ) :
    Continuous (glyzCoordinateWeight e A b) := by
  unfold glyzCoordinateWeight glyzIsotropicWeight
  exact continuous_const.mul ((continuous_glyzDecayWeight A).comp
    (continuous_const.smul ((EuclideanSpace.equiv (Fin l) ℝ).continuous.comp e.continuous)))

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
theorem glyzCoordinateWeight_neg {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l) (A : ℕ) (b : ℝ) (z : H) :
    glyzCoordinateWeight e A b (-z) = glyzCoordinateWeight e A b z := by
  simp only [glyzCoordinateWeight, glyzIsotropicWeight, glyzDecayWeight,
    map_neg, smul_neg, norm_neg]

theorem integrable_glyzCoordinateWeight {l A : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l)
    (hA : l < A) {b : ℝ} (hb : 0 < b) : Integrable (glyzCoordinateWeight e A b) := by
  exact e.measurePreserving.integrable_comp_of_integrable
    ((PiLp.volume_preserving_ofLp (Fin l)).integrable_comp_of_integrable
      (integrable_glyzIsotropicWeight hA hb))

theorem integral_glyzCoordinateWeight {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l)
    (A : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ z, glyzCoordinateWeight e A b z) = ∫ z : Base l, glyzDecayWeight A z := by
  unfold glyzCoordinateWeight
  rw [e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun z => glyzIsotropicWeight A b ((EuclideanSpace.equiv (Fin l) ℝ) z))]
  have hp : MeasurePreserving (EuclideanSpace.equiv (Fin l) ℝ) volume volume :=
    PiLp.volume_preserving_ofLp (Fin l)
  rw [hp.integral_comp (EuclideanSpace.equiv (Fin l) ℝ).toHomeomorph.measurableEmbedding
    (glyzIsotropicWeight A b), integral_glyzIsotropicWeight A hb]

theorem glyz_isNegInvariant_withDensity {w : H → ℝ≥0∞} (hw : ∀ x, w (-x) = w x) :
    Measure.IsNegInvariant (volume.withDensity w) := by
  constructor
  apply Measure.ext
  intro s hs
  change (Measure.map (fun x : H => -x) (volume.withDensity w)) s = _
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_neg hs),
    ← lintegral_indicator hs]
  convert lintegral_neg_eq_self (μ := (volume : Measure H)) (fun x => s.indicator w x) using 1
  apply lintegral_congr
  intro x
  by_cases hx : -x ∈ s <;> simp [hx, hw]

def glyzCoordinateMeasure {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l) (A : ℕ) (b : ℝ) : Measure H :=
  volume.withDensity (fun z => ENNReal.ofReal (glyzCoordinateWeight e A b z))

theorem isFiniteMeasure_glyzCoordinateMeasure {l A : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l)
    (hA : l < A) {b : ℝ} (hb : 0 < b) : IsFiniteMeasure (glyzCoordinateMeasure e A b) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_glyzCoordinateWeight e hA hb)
    (Filter.Eventually.of_forall fun z => (mul_pos (pow_pos hb l) (glyzDecayWeight_pos _ _)).le)]
  exact ENNReal.ofReal_ne_top

instance isNegInvariant_glyzCoordinateMeasure {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l) (A : ℕ) (b : ℝ) :
    Measure.IsNegInvariant (glyzCoordinateMeasure e A b) :=
  glyz_isNegInvariant_withDensity (fun z => congrArg ENNReal.ofReal (glyzCoordinateWeight_neg e A b z))

theorem glyzCoordinateMeasure_average {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {l : ℕ} (e : H ≃ₗᵢ[ℝ] GlyzSpace l) (A : ℕ) (b : ℝ)
    (S : H →L[ℝ] E) {F : E → ℝ≥0∞} (hF : Measurable F) (x : E) :
    glyzSubspaceAverage (glyzCoordinateMeasure e A b) S F x =
      ∫⁻ z : Base l, ENNReal.ofReal (glyzIsotropicWeight A b z) *
        F (x - S (e.symm ((EuclideanSpace.equiv (Fin l) ℝ).symm z))) := by
  unfold glyzSubspaceAverage glyzCoordinateMeasure
  have hf : Measurable (fun y => F (x - S y)) :=
    hF.comp (continuous_const.sub S.continuous).measurable
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (continuous_glyzCoordinateWeight e A b).measurable.ennreal_ofReal hf]
  let T : Base l ≃L[ℝ] H := (EuclideanSpace.equiv (Fin l) ℝ).symm.trans
    e.symm.toContinuousLinearEquiv
  have hp : MeasurePreserving T volume volume :=
    e.symm.measurePreserving.comp (PiLp.volume_preserving_toLp (Fin l))
  rw [← hp.lintegral_comp_emb T.toHomeomorph.measurableEmbedding]
  apply lintegral_congr
  intro z
  simp only [T, ContinuousLinearEquiv.trans_apply, Pi.mul_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, glyzCoordinateWeight,
    LinearIsometryEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

end PlanarNikodym
