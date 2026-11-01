import PlanarNikodym.Analysis.Fourier.IntegrablePartialPlancherel

/-! Compact time slices of the actual band data are L¹ and L², even
when the original input is merely integrable. This supplies honest
integral inputs for the cone operator without a smoothness hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem memLp_timeLocalizedData_two (b δ : ℝ) (i : ℕ)
    {h : Plane → ℂ} (h2 : MemLp h 2) : MemLp (timeLocalizedData b δ i h) 2 := by
  apply h2.mono
  · exact ((Complex.continuous_ofReal.comp
      ((contDiff_scaleTimeCutoff b δ i).continuous.comp continuous_fst)).aestronglyMeasurable).mul
      h2.aestronglyMeasurable
  · filter_upwards [] with x
    simp only [timeLocalizedData, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (scaleTimeCutoff_nonneg b δ x.1 i)]
    exact mul_le_of_le_one_left (norm_nonneg _) (scaleTimeCutoff_le_one b δ x.1 i)

theorem hasCompactSupport_timeLocalizedData_of_vertical
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) {h : Plane → ℂ}
    {K : Set ℝ} (hK : IsCompact K) (hv : ∀ x : Plane, x.2 ∉ K → h x = 0) :
    HasCompactSupport (timeLocalizedData b δ i h) := by
  apply HasCompactSupport.intro ((hasCompactSupport_scaleTimeCutoff b hδ i).prod hK)
  intro x hx
  by_cases ht : x.1 ∈ tsupport (scaleTimeCutoff b δ i)
  · have hη : x.2 ∉ K := fun hη => hx ⟨ht, hη⟩
    simp only [timeLocalizedData, hv x hη, mul_zero]
  · have hz := image_eq_zero_of_notMem_tsupport ht
    simp only [timeLocalizedData, hz, Complex.ofReal_zero, zero_mul]

theorem integrable_timeLocalizedData_of_vertical
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) {h : Plane → ℂ}
    (h2 : MemLp h 2) {K : Set ℝ} (hK : IsCompact K)
    (hv : ∀ x : Plane, x.2 ∉ K → h x = 0) :
    Integrable (timeLocalizedData b δ i h) := by
  have hc := hasCompactSupport_timeLocalizedData_of_vertical b hδ i hK hv
  apply memLp_one_iff_integrable.mp
  exact (memLp_timeLocalizedData_two b δ i h2).mono_exponent_of_measure_support_ne_top
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx) hc.measure_ne_top (by norm_num)

theorem memLp_weightedPartialFourierData_two {m : Plane → ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) {f : Plane → ℂ}
    (h1 : Integrable f) {r : ℝ} (hr : 0 < r) :
    MemLp (fun x : Plane => weightedPartialFourierData m f r x.1 x.2) 2 := by
  have ha := weighted_scaledFourierData_continuous hm h1 r
  have hac : HasCompactSupport (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) :=
    (hc.comp_left (g := Complex.ofRealCLM) rfl).mul_right
  have h2 : MemLp (fun ξ : Plane => (m ξ : ℂ) * planeFourierIntegral f (r • ξ)) 2 :=
    ha.memLp_of_hasCompactSupport hac
  refine ⟨(stronglyMeasurable_partialFourierData ha r).aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).2
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_weightedPartialFourierData_sq_of_integrable hm hc h1 hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h2.2)

theorem weightedPartialFourierData_eq_zero_of_vertical {m : Plane → ℝ}
    {f : Plane → ℂ} (r t η : ℝ) (hη : η ∉ Prod.snd '' tsupport m) :
    weightedPartialFourierData m f r t η = 0 := by
  unfold weightedPartialFourierData partialFourierData
  have hz (ξ : ℝ) : m (ξ, η) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem => hη ⟨(ξ, η), hmem, rfl⟩)
  simp only [hz, Complex.ofReal_zero, zero_mul, integral_zero]

/-- The actual compact symbol transfers its vertical frequency gap to
the partial inverse data pointwise, without approximation. -/
theorem weightedPartialFourierData_eq_zero_of_gap {m : Plane → ℝ}
    {f : Plane → ℂ} {a : ℝ} (hgap : ∀ ξ : Plane, |ξ.2| < a → m ξ = 0)
    (r t η : ℝ) (hη : |η| < a) : weightedPartialFourierData m f r t η = 0 := by
  unfold weightedPartialFourierData partialFourierData
  simp only [hgap (_, η) hη, Complex.ofReal_zero, zero_mul, integral_zero]

theorem timeLocalized_weightedPartialFourierData_eq_zero_of_gap {m : Plane → ℝ}
    {f : Plane → ℂ} {a : ℝ} (hgap : ∀ ξ : Plane, |ξ.2| < a → m ξ = 0)
    (r b δ : ℝ) (i : ℕ) (x : Plane) (hx : |x.2| < a) :
    timeLocalizedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2) x = 0 := by
  simp only [timeLocalizedData, weightedPartialFourierData_eq_zero_of_gap hgap r x.1 x.2 hx,
    mul_zero]

theorem integrable_timeLocalized_weightedPartialFourierData
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) {m : Plane → ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) {f : Plane → ℂ}
    (h1 : Integrable f) {r : ℝ} (hr : 0 < r) :
    Integrable (timeLocalizedData b δ i (fun x => weightedPartialFourierData m f r x.1 x.2)) :=
  integrable_timeLocalizedData_of_vertical b hδ i (memLp_weightedPartialFourierData_two hm hc h1 hr)
    (hc.isCompact.image continuous_snd)
    (fun x hx => weightedPartialFourierData_eq_zero_of_vertical r x.1 x.2 hx)

end PlanarNikodym
