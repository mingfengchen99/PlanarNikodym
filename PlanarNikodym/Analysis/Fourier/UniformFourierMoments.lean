import PlanarNikodym.Analysis.Fourier.UniformAmplitudeFourier

/-! Uniform weighted moments of actual Fourier coefficients. Fixed compact
symbol support and full derivative bounds give every polynomial moment,
and hence arbitrarily rapid integrated tails. The coefficients are the
true Schwartz Fourier transform, not a postulated expansion. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace PlanarNikodym

theorem exists_uniform_compact_schwartz_seminorm_image_bound
    {P E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : SchwartzMap E ℂ →L[ℝ] SchwartzMap V ℂ) (S : P → SchwartzMap E ℂ)
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, SchwartzMap.seminorm ℝ k n (T (S p)) ≤ C := by
  let q : Seminorm ℝ (SchwartzMap E ℂ) :=
    (SchwartzMap.seminorm ℝ k n).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ V ℂ).continuous_seminorm (k, n)).comp T.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ E ℂ) q hq
  choose B hB hderiv using hjet
  choose D hD hsemi using fun i : ℕ × ℕ =>
    exists_uniform_schwartz_seminorm_bound S hK hs i.2 i.1
      (fun _ => B i.2) (fun _ => hB i.2) (fun p x => hderiv i.2 p x)
  refine ⟨(C : ℝ) * ∑ i ∈ s, D i * B i.2,
    mul_nonneg C.coe_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hD i) (hB i.2)), ?_⟩
  intro p
  apply (hC (S p)).trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i _ => mul_nonneg (hD i) (hB i.2))
  intro i hi
  exact (hsemi i p).trans (Finset.single_le_sum
    (fun j _ => mul_nonneg (hD j) (hB j.2)) hi)

/-- Every polynomial moment of the coefficient norm is uniformly finite. -/
theorem exists_uniform_compact_schwartz_image_moment_bound
    {P E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure V) [μ.HasTemperateGrowth]
    (T : SchwartzMap E ℂ →L[ℝ] SchwartzMap V ℂ) (S : P → SchwartzMap E ℂ)
    {K : Set E} (hK : IsCompact K) (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, (∫ x, ‖x‖ ^ k * ‖T (S p) x‖ ∂μ) ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_uniform_compact_schwartz_seminorm_image_bound
    T S hK hs hjet 0 0
  obtain ⟨C₁, hC₁, h₁⟩ := exists_uniform_compact_schwartz_seminorm_image_bound
    T S hK hs hjet (k + μ.integrablePower) 0
  let D : ℝ := 2 ^ μ.integrablePower *
    (∫ x, (1 + ‖x‖) ^ (-(μ.integrablePower : ℝ)) ∂μ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D * (C₀ + C₁), mul_nonneg hD (add_nonneg hC₀ hC₁), fun p => ?_⟩
  have hh := (T (S p)).integral_pow_mul_iteratedFDeriv_le ℝ μ k 0
  simp only [norm_iteratedFDeriv_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (h₀ p) (h₁ p)) hD)

/-- Actual two-dimensional Fourier coefficients inherit all uniform
weighted L¹ bounds from compact symbol jets. -/
theorem exists_uniform_input_fourier_moment_bound
    {P : Type*} (S : P → SchwartzMap FourierPlane ℂ)
    {K : Set FourierPlane} (hK : IsCompact K) (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, (∫ ξ : FourierPlane, ‖ξ‖ ^ k * ‖𝓕 (S p) ξ‖) ≤ C :=
  exists_uniform_compact_schwartz_image_moment_bound volume
    ((FourierTransform.fourierCLM ℂ (SchwartzMap FourierPlane ℂ)).restrictScalars ℝ)
    S hK hs hjet k

/-- A higher actual moment controls the coefficient tail outside any
positive radius. This produces arbitrary tail order without truncating
Fourier inversion or postulating a decay estimate. -/
theorem schwartz_integral_moment_tail_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure V) [μ.HasTemperateGrowth] (f : SchwartzMap V ℂ)
    (k M : ℕ) {R : ℝ} (hR : 0 < R) :
    (∫ x in {x : V | R ≤ ‖x‖}, ‖x‖ ^ k * ‖f x‖ ∂μ) ≤
      (R⁻¹) ^ M * ∫ x, ‖x‖ ^ (k + M) * ‖f x‖ ∂μ := by
  have hpoint (x : V) (hx : R ≤ ‖x‖) :
      ‖x‖ ^ k * ‖f x‖ ≤ (R⁻¹) ^ M * (‖x‖ ^ (k + M) * ‖f x‖) := by
    have hh : (R ^ M) * (‖x‖ ^ k * ‖f x‖) ≤ ‖x‖ ^ (k + M) * ‖f x‖ := by
      have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hx M)
        (mul_nonneg (pow_nonneg (norm_nonneg x) k) (norm_nonneg (f x)))
      simpa only [pow_add] using hp.trans_eq (by ring)
    have hi := mul_le_mul_of_nonneg_left hh (show 0 ≤ (R⁻¹) ^ M by positivity)
    simpa only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hR.ne', one_pow, one_mul] using hi
  have hf := f.integrable_pow_mul μ k
  have hg := f.integrable_pow_mul μ (k + M)
  calc
    _ ≤ ∫ x in {x : V | R ≤ ‖x‖}, (R⁻¹) ^ M * (‖x‖ ^ (k + M) * ‖f x‖) ∂μ :=
      setIntegral_mono_on hf.integrableOn (hg.const_mul _).integrableOn
        (isClosed_le continuous_const continuous_norm).measurableSet hpoint
    _ ≤ ∫ x, (R⁻¹) ^ M * (‖x‖ ^ (k + M) * ‖f x‖) ∂μ :=
      setIntegral_le_integral (hg.const_mul _) (ae_of_all _ fun x => by positivity)
    _ = _ := integral_const_mul _ _

theorem exists_uniform_input_fourier_tail_bound
    {P : Type*} (S : P → SchwartzMap FourierPlane ℂ)
    {K : Set FourierPlane} (hK : IsCompact K) (hs : ∀ p, tsupport (S p) ⊆ K)
    (hjet : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, ‖iteratedFDeriv ℝ n (S p) x‖ ≤ B)
    (k M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p R, 0 < R →
      (∫ ξ in {ξ : FourierPlane | R ≤ ‖ξ‖}, ‖ξ‖ ^ k * ‖𝓕 (S p) ξ‖) ≤
        C * (R⁻¹) ^ M := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_input_fourier_moment_bound S hK hs hjet (k + M)
  refine ⟨C, hC, fun p R hR => ?_⟩
  exact (schwartz_integral_moment_tail_le volume (𝓕 (S p)) k M hR).trans
    ((mul_le_mul_of_nonneg_left (hb p) (by positivity)).trans_eq (mul_comm _ _))

end PlanarNikodym
