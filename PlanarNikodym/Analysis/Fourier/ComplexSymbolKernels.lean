import PlanarNikodym.Analysis.Fourier.SchwartzFamilyBounds
import PlanarNikodym.Analysis.Fourier.BandOscillatoryRepresentation

/-! Actual complex-symbol inverse Fourier kernels on the product-norm
plane. Uniform rapid derivative bounds for a fixed compact symbol support
give uniform rapid Lp kernel bounds, including p = ∞. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal

namespace PlanarNikodym

/-- The actual inverse transform, transporting only the Fourier calculation
to Euclidean coordinates and then returning to the original plane. -/
def planeInverseFourierSchwartzCLM :
    SchwartzMap Plane ℂ →L[ℂ] SchwartzMap Plane ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv.symm).comp
    ((FourierTransform.fourierInvCLM ℂ (SchwartzMap FourierPlane ℂ)).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv))

theorem planeInverseFourierSchwartzCLM_apply (f : SchwartzMap Plane ℂ) (x : Plane) :
    planeInverseFourierSchwartzCLM f x =
      ∫ ξ : Plane, f ξ * planeFourierCharacter x ξ := by
  change (𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ fourierPlaneEquiv f))
    (WithLp.toLp 2 x) = _
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  rw [← (WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
    (MeasurableEquiv.toLp 2 Plane).symm.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, fourierPlaneEquiv,
    WithLp.prodContinuousLinearEquiv_apply, WithLp.prod_inner_apply,
    RCLike.inner_apply, conj_trivial, smul_eq_mul, planeFourierCharacter, fourierPhase]
  rw [mul_comm]

/-- The Lp norm of the actual inverse kernel decays to every order once
the full derivatives of the symbol do so on one fixed compact support.
The kernel constant is uniform in all parameters and in r ≥ 1. -/
theorem exists_uniform_complex_symbol_kernel_Lp_decay
    {P : Type*} (S : P → ℝ → SchwartzMap Plane ℂ)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ p r, tsupport (S p r) ⊆ K)
    (hdecay : ∀ n N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p r, 1 ≤ r →
      ∀ ξ, ‖iteratedFDeriv ℝ n (S p r) ξ‖ ≤ C * (r⁻¹) ^ N)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q r, 1 ≤ r →
      eLpNorm (planeInverseFourierSchwartzCLM (S q r)) p volume ≤
        ENNReal.ofReal (C * (r⁻¹) ^ N) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let T : SchwartzMap Plane ℂ →L[ℝ] Lp ℂ p (volume : Measure Plane) :=
    (SchwartzMap.toLpCLM ℝ ℂ p volume).comp
      (planeInverseFourierSchwartzCLM.restrictScalars ℝ)
  obtain ⟨C, hC, hb⟩ := exists_compact_schwartz_clm_decay_constant T S hK hs hdecay N
  refine ⟨C, hC, ?_⟩
  intro q r hr
  let f := planeInverseFourierSchwartzCLM (S q r)
  have he : eLpNorm f p volume = ENNReal.ofReal ‖f.toLp p volume‖ := by
    rw [SchwartzMap.norm_toLp, ENNReal.ofReal_toReal (f.memLp p volume).eLpNorm_ne_top]
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hb q r hr)

end PlanarNikodym
