import PlanarNikodym.Analysis.Fourier.GlyzSchwartzRescaling

/-! Exact affine invariance of an actual finite decoupling inequality.
The transformed pieces are constructed from the original Fourier
transforms; the common determinant factor cancels on both sides. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def glyzAffineLpFactor (L : E ≃L[ℝ] E) (p : ℝ≥0∞) : ℝ :=
  |LinearMap.det L.toLinearMap| * |(LinearMap.det L.toLinearMap)⁻¹| ^ (1 / p.toReal)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem glyzAffineLpFactor_pos (L : E ≃L[ℝ] E) (p : ℝ≥0∞) : 0 < glyzAffineLpFactor L p := by
  have hd := (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  exact mul_pos (abs_pos.mpr hd) (Real.rpow_pos_of_pos (abs_pos.mpr (inv_ne_zero hd)) _)

theorem lpNorm_glyzSchwartzFrequencyAffine (L : E ≃L[ℝ] E) (a : E)
    (f : SchwartzMap E ℂ) (p : ℝ≥0∞) :
    lpNorm (glyzSchwartzFrequencyAffine L a f : E → ℂ) p volume =
      glyzAffineLpFactor L p * lpNorm (f : E → ℂ) p volume := by
  have h := congrArg ENNReal.toReal (eLpNorm_glyzSchwartzFrequencyAffine L a f p)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _),
    toReal_eLpNorm (f.memLp p volume).aestronglyMeasurable,
    toReal_eLpNorm ((glyzSchwartzFrequencyAffine L a f).memLp p volume).aestronglyMeasurable,
    glyzAffineLpFactor, mul_assoc] using h

theorem glyzSchwartzFrequencyAffine_sum (L : E ≃L[ℝ] E) (a : E) (I : Finset ℕ)
    (f : ℕ → SchwartzMap E ℂ) :
    glyzSchwartzFrequencyAffine L a (∑ i ∈ I, f i) =
      ∑ i ∈ I, glyzSchwartzFrequencyAffine L a (f i) := by
  ext x
  simp only [glyzSchwartzFrequencyAffine_apply, sum_apply, Finset.smul_sum, Finset.mul_sum]

theorem glyz_affine_decoupling_transfer (L : E ≃L[ℝ] E) (a : E) (I : Finset ℕ)
    (f : ℕ → SchwartzMap E ℂ) (p : ℝ≥0∞) (D : ℝ)
    (h : lpNorm ((∑ i ∈ I, glyzSchwartzFrequencyAffine L a (f i) : SchwartzMap E ℂ) : E → ℂ)
        p volume ^ (2 : ℕ) ≤
      D * ∑ i ∈ I, lpNorm (glyzSchwartzFrequencyAffine L a (f i) : E → ℂ) p volume ^ (2 : ℕ)) :
    lpNorm ((∑ i ∈ I, f i : SchwartzMap E ℂ) : E → ℂ) p volume ^ (2 : ℕ) ≤
      D * ∑ i ∈ I, lpNorm (f i : E → ℂ) p volume ^ (2 : ℕ) := by
  rw [← glyzSchwartzFrequencyAffine_sum] at h
  simp_rw [lpNorm_glyzSchwartzFrequencyAffine, mul_pow] at h
  rw [← Finset.mul_sum] at h
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (glyzAffineLpFactor_pos L p))).mp
  nlinarith [h]

end PlanarNikodym
