import PlanarNikodym.Analysis.Fourier.TimeLocalizedIntegrability
import PlanarNikodym.Analysis.Fourier.TimeSliceExtension

/-! Restrict data to the closed time-window supports. The original
window remains in the amplitude exactly once. Threefold support overlap
gives a uniform input square sum for those actual oscillatory slices. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Classical
namespace PlanarNikodym

def timeRestrictedData (b δ : ℝ) (i : ℕ) (h : Plane → ℂ) : Plane → ℂ :=
  (Prod.fst ⁻¹' tsupport (scaleTimeCutoff b δ i)).indicator h

theorem stronglyMeasurable_timeRestrictedData (b δ : ℝ) (i : ℕ)
    {h : Plane → ℂ} (hh : StronglyMeasurable h) :
    StronglyMeasurable (timeRestrictedData b δ i h) :=
  hh.indicator ((isClosed_tsupport _).preimage continuous_fst).measurableSet

theorem memLp_timeRestrictedData_two (b δ : ℝ) (i : ℕ)
    {h : Plane → ℂ} (h2 : MemLp h 2) : MemLp (timeRestrictedData b δ i h) 2 :=
  h2.indicator ((isClosed_tsupport _).preimage continuous_fst).measurableSet

theorem hasCompactSupport_timeRestrictedData_of_vertical
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) {h : Plane → ℂ}
    {K : Set ℝ} (hK : IsCompact K) (hv : ∀ x : Plane, x.2 ∉ K → h x = 0) :
    HasCompactSupport (timeRestrictedData b δ i h) := by
  apply HasCompactSupport.intro ((hasCompactSupport_scaleTimeCutoff b hδ i).prod hK)
  intro x hx
  by_cases ht : x.1 ∈ tsupport (scaleTimeCutoff b δ i)
  · have hη : x.2 ∉ K := fun hη => hx ⟨ht, hη⟩
    simp only [timeRestrictedData, indicator_apply, mem_preimage, ht, if_true, hv x hη]
  · simp only [timeRestrictedData, indicator_apply, mem_preimage, ht, if_false]

theorem integrable_timeRestrictedData_of_vertical
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) {h : Plane → ℂ}
    (h2 : MemLp h 2) {K : Set ℝ} (hK : IsCompact K)
    (hv : ∀ x : Plane, x.2 ∉ K → h x = 0) :
    Integrable (timeRestrictedData b δ i h) := by
  have hc := hasCompactSupport_timeRestrictedData_of_vertical b hδ i hK hv
  apply memLp_one_iff_integrable.mp
  exact (memLp_timeRestrictedData_two b δ i h2).mono_exponent_of_measure_support_ne_top
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx) hc.measure_ne_top (by norm_num)

theorem sum_timeRestrictedData_enorm_sq_le (b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) (h : Plane → ℂ) (x : Plane) :
    (∑ i ∈ Finset.range N, ‖timeRestrictedData b δ i h x‖ₑ ^ (2 : ℕ)) ≤
      (3 : ℝ≥0∞) * ‖h x‖ₑ ^ (2 : ℕ) := by
  have he (i : ℕ) : ‖timeRestrictedData b δ i h x‖ₑ ^ (2 : ℕ) =
      if x.1 ∈ tsupport (scaleTimeCutoff b δ i) then ‖h x‖ₑ ^ (2 : ℕ) else 0 := by
    by_cases ht : x.1 ∈ tsupport (scaleTimeCutoff b δ i) <;>
      simp [timeRestrictedData, ht]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_left (by exact_mod_cast scaleTimeCutoff_overlap_le_three b hδ N x.1) _

theorem sum_lintegral_timeRestrictedData_sq_le (b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) {h : Plane → ℂ} (hh : StronglyMeasurable h) :
    (∑ i ∈ Finset.range N, ∫⁻ x : Plane, ‖timeRestrictedData b δ i h x‖ₑ ^ (2 : ℕ)) ≤
      (3 : ℝ≥0∞) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) := by
  rw [← lintegral_finsetSum _ (fun i _ =>
    (stronglyMeasurable_timeRestrictedData b δ i hh).enorm.pow_const _),
    ← lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
  exact lintegral_mono (sum_timeRestrictedData_enorm_sq_le b hδ N h)

/-- Restricting the input does not insert a second copy of the smooth
window: the original slice integral is literally unchanged. -/
theorem timeSliceExtension_timeRestrictedData {P : Type}
    (Φ : P × ℝ → ℝ) (a : P × ℝ × ℝ → ℂ) (h : Plane → ℂ)
    (r b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) (p : P) :
    timeSliceExtension Φ a (timeRestrictedData b δ i h) r (b + (i : ℝ) * δ) δ p =
      timeSliceExtension Φ a h r (b + (i : ℝ) * δ) δ p := by
  unfold timeSliceExtension
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with t
  have hw : timePartitionWindow ((t - (b + (i : ℝ) * δ)) / δ) = scaleTimeCutoff b δ i t := by
    unfold scaleTimeCutoff
    congr 1
    field_simp
    ring
  rw [hw]
  by_cases ht : t ∈ tsupport (scaleTimeCutoff b δ i)
  · simp [timeRestrictedData, ht]
  · have hz := image_eq_zero_of_notMem_tsupport ht
    simp [timeRestrictedData, ht, hz]

theorem integrable_timeRestricted_weightedPartialFourierData
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ) {m : Plane → ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) {f : Plane → ℂ}
    (h1 : Integrable f) {r : ℝ} (hr : 0 < r) :
    Integrable (timeRestrictedData b δ i (fun x => weightedPartialFourierData m f r x.1 x.2)) :=
  integrable_timeRestrictedData_of_vertical b hδ i (memLp_weightedPartialFourierData_two hm hc h1 hr)
    (hc.isCompact.image continuous_snd)
    (fun x hx => weightedPartialFourierData_eq_zero_of_vertical r x.1 x.2 hx)

theorem timeRestrictedData_eq_zero_of_gap {h : Plane → ℂ} {a : ℝ}
    (hgap : ∀ x : Plane, |x.2| < a → h x = 0) (b δ : ℝ) (i : ℕ)
    (x : Plane) (hx : |x.2| < a) : timeRestrictedData b δ i h x = 0 := by
  simp [timeRestrictedData, indicator_apply, hgap x hx]

/-- The input square sum appropriate to the original windowed slice:
the window is not multiplied into the data for a second time. -/
theorem sum_lintegral_timeRestricted_weightedPartial_sq_le
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) {m : Plane → ℝ}
    (hm : Continuous m) (hc : HasCompactSupport m) {f : Plane → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) {r M : ℝ} (hr : 0 < r)
    (hbound : ∀ ξ : Plane, |m ξ| ≤ M) :
    (∑ i ∈ Finset.range N, ∫⁻ x : Plane,
      ‖timeRestrictedData b δ i (fun y => weightedPartialFourierData m f r y.1 y.2) x‖ₑ ^
        (2 : ℕ)) ≤
      (3 : ℝ≥0∞) * (ENNReal.ofReal (M ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ)) *
        ∫⁻ x : Plane, ‖f x‖ₑ ^ (2 : ℕ)) := by
  calc
    _ ≤ (3 : ℝ≥0∞) * ∫⁻ x : Plane, ‖weightedPartialFourierData m f r x.1 x.2‖ₑ ^ (2 : ℕ) :=
      sum_lintegral_timeRestrictedData_sq_le b hδ N
        (stronglyMeasurable_partialFourierData (weighted_scaledFourierData_continuous hm h1 r) r)
    _ ≤ _ := mul_le_mul_right
      (lintegral_weightedPartialFourierData_sq_le_of_integrable hm hc h1 h2 hr hbound) _

end PlanarNikodym
