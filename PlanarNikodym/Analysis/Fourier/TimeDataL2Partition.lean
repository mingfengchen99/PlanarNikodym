import PlanarNikodym.Analysis.Fourier.PartialPlancherel

/-! The actual smooth time windows have a squared-sum bound of one.
Consequently localization of the input data costs no factor depending on
the number or width of the time pieces. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal NNReal Classical
namespace PlanarNikodym

/-- The positive telescoping partition is sub-unital at every time,
including times outside the interval where its sum is exactly one. -/
theorem sum_scaleTimeCutoff_le_one (a δ t : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t) ≤ 1 := by
  rw [sum_scaleTimeCutoff]
  exact (sub_le_self _ (Real.smoothTransition.nonneg _)).trans
    (Real.smoothTransition.le_one _)

theorem sum_scaleTimeCutoff_sq_le_one (a δ t : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (scaleTimeCutoff a δ i t) ^ (2 : ℕ)) ≤ 1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, scaleTimeCutoff a δ i t := by
      apply Finset.sum_le_sum
      intro i _
      have h₀ := scaleTimeCutoff_nonneg a δ t i
      have h₁ := scaleTimeCutoff_le_one a δ t i
      nlinarith
    _ ≤ 1 := sum_scaleTimeCutoff_le_one a δ t N

/-- The actual input multiplier attached to the `i`th time slice. -/
def timeLocalizedData (a δ : ℝ) (i : ℕ) (h : Plane → ℂ) (x : Plane) : ℂ :=
  (scaleTimeCutoff a δ i x.1 : ℂ) * h x

theorem stronglyMeasurable_timeLocalizedData (a δ : ℝ) (i : ℕ)
    {h : Plane → ℂ} (hh : StronglyMeasurable h) :
    StronglyMeasurable (timeLocalizedData a δ i h) :=
  ((Complex.continuous_ofReal.comp
    ((contDiff_scaleTimeCutoff a δ i).continuous.comp continuous_fst)).stronglyMeasurable).mul hh

theorem sum_timeLocalizedData_enorm_sq_le (a δ : ℝ) (N : ℕ)
    (h : Plane → ℂ) (x : Plane) :
    (∑ i ∈ Finset.range N, ‖timeLocalizedData a δ i h x‖ₑ ^ (2 : ℕ)) ≤
      ‖h x‖ₑ ^ (2 : ℕ) := by
  have he : ∀ i, ‖timeLocalizedData a δ i h x‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal ((scaleTimeCutoff a δ i x.1) ^ (2 : ℕ)) * ‖h x‖ₑ ^ (2 : ℕ) := by
    intro i
    rw [timeLocalizedData, enorm_mul, mul_pow,
      ← ofReal_norm ((scaleTimeCutoff a δ i x.1 : ℝ) : ℂ), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (scaleTimeCutoff_nonneg a δ x.1 i),
      ENNReal.ofReal_pow (scaleTimeCutoff_nonneg a δ x.1 i)]
  simp_rw [he]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  calc
    _ ≤ ENNReal.ofReal 1 * ‖h x‖ₑ ^ (2 : ℕ) :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal (sum_scaleTimeCutoff_sq_le_one a δ x.1 N)) _
    _ = _ := by simp

/-- The sum of genuine L² masses of all localized data is bounded by the
original mass, uniformly in every time scale and every number of pieces. -/
theorem sum_lintegral_timeLocalizedData_sq_le (a δ : ℝ) (N : ℕ)
    {h : Plane → ℂ} (hh : StronglyMeasurable h) :
    (∑ i ∈ Finset.range N, ∫⁻ x : Plane, ‖timeLocalizedData a δ i h x‖ₑ ^ (2 : ℕ)) ≤
      ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  rw [← lintegral_finsetSum _ (fun i _ =>
    (stronglyMeasurable_timeLocalizedData a δ i hh).enorm.pow_const _)]
  exact lintegral_mono (sum_timeLocalizedData_enorm_sq_le a δ N h)

/-- The same estimate in squared `eLpNorm` form. -/
theorem sum_timeLocalizedData_eLpNorm_two_sq_le (a δ : ℝ) (N : ℕ)
    {h : Plane → ℂ} (hh : StronglyMeasurable h) :
    (∑ i ∈ Finset.range N, eLpNorm (timeLocalizedData a δ i h) 2 volume ^ (2 : ℕ)) ≤
      eLpNorm h 2 volume ^ (2 : ℕ) := by
  have he (f : Plane → ℂ) : eLpNorm f 2 volume ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume) (p := (2 : ℝ≥0)) (by norm_num))
  simp_rw [he]
  exact sum_lintegral_timeLocalizedData_sq_le a δ N hh

/-- Plancherel and time partition together, with the true compact frequency
amplitude and the exact inverse frequency factor. -/
theorem sum_lintegral_timeLocalized_partialFourierData_sq_le (b δ : ℝ) (N : ℕ)
    (a : Plane → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {r : ℝ} (hr : 0 < r) :
    (∑ i ∈ Finset.range N, ∫⁻ x : Plane,
      ‖timeLocalizedData b δ i (fun y => partialFourierData a r y.1 y.2) x‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal r⁻¹ * ∫⁻ ξ : Plane, ‖a ξ‖ₑ ^ (2 : ℕ) := by
  calc
    _ ≤ ∫⁻ x : Plane, ‖partialFourierData a r x.1 x.2‖ₑ ^ (2 : ℕ) :=
      sum_lintegral_timeLocalizedData_sq_le b δ N
        (stronglyMeasurable_partialFourierData ha.continuous r)
    _ = _ := lintegral_partialFourierData_plane_sq a ha hc hr

end PlanarNikodym
