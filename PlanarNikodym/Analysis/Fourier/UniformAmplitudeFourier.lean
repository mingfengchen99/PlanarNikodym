import PlanarNikodym.Analysis.Fourier.JointAmplitudeFourier

/-! Uniform constants for the actual joint Fourier coefficients.  Fixed
compact support and bounds for the full derivatives of the amplitudes
give one integrable-coefficient constant for the entire family. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace PlanarNikodym

def jointAmplitudeFourierCLM :
    SchwartzMap (Plane × Plane) ℂ →L[ℂ] SchwartzMap AmplitudeFourierSpace ℂ :=
  (FourierTransform.fourierCLM ℂ (SchwartzMap AmplitudeFourierSpace ℂ)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ amplitudeFourierEquiv)

@[simp] theorem jointAmplitudeFourierCLM_apply (b : SchwartzMap (Plane × Plane) ℂ) :
    jointAmplitudeFourierCLM b = jointAmplitudeFourier b := rfl

/-- Compact support and actual full-derivative bounds give a uniform
bound after any fixed continuous linear Schwartz map. -/
theorem exists_uniform_compact_schwartz_clm_bound
    {P E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : SchwartzMap E F →L[ℝ] V) (S : P → SchwartzMap E F)
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖T (S p)‖ ≤ C := by
  obtain ⟨s, C, hC, hT⟩ := exists_schwartz_clm_finite_bound T
  choose B hB hderiv using hjet
  choose A hA hsemi using fun i : ℕ × ℕ =>
    exists_uniform_schwartz_seminorm_bound S hK hs i.2 i.1
      (fun _ => B i.2) (fun _ => hB i.2) (fun p x => hderiv i.2 p x)
  refine ⟨C * ∑ i ∈ s, A i * B i.2,
    mul_nonneg hC (Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (hB i.2)), ?_⟩
  intro p
  exact (hT (S p)).trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => hsemi i p) hC)

/-- One constant controls the L¹ mass of every actual Fourier
coefficient family, with no parameter-dependent support expansion. -/
theorem exists_uniform_jointAmplitudeFourier_L1_bound
    {P : Type*} (S : P → SchwartzMap (Plane × Plane) ℂ)
    {K : Set (Plane × Plane)} (hK : IsCompact K)
    (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier (S p) ζ‖ₑ) ≤
        ENNReal.ofReal C := by
  let T : SchwartzMap (Plane × Plane) ℂ →L[ℝ]
      Lp ℂ 1 (volume : Measure AmplitudeFourierSpace) :=
    (SchwartzMap.toLpCLM ℝ ℂ 1 volume).comp
      (jointAmplitudeFourierCLM.restrictScalars ℝ)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_compact_schwartz_clm_bound T S hK hs hjet
  refine ⟨C, hC, ?_⟩
  intro p
  have he : (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier (S p) ζ‖ₑ) =
      ENNReal.ofReal ‖T (S p)‖ := by
    change _ = ENNReal.ofReal ‖(jointAmplitudeFourier (S p)).toLp 1 volume‖
    rw [SchwartzMap.norm_toLp, ENNReal.ofReal_toReal
      ((jointAmplitudeFourier (S p)).memLp 1 volume).eLpNorm_ne_top,
      eLpNorm_one_eq_lintegral_enorm]
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hbound p)

end PlanarNikodym
