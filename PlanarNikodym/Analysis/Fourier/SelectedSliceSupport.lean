import PlanarNikodym.Analysis.Localization.SelectedTimeSliceCoordinates
import PlanarNikodym.Analysis.Fourier.PartialExtensionLocalization

/-! The original slice vanishes outside the actual selected-parameter
fibre of its joint compact chart. Thus the proved chart-restricted L²
bound is the full selected-parameter L² bound for each frozen parameter. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem selectedParameterLift_frozen_selected {d m : ℕ}
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2)) (t : ℝ)
    (z : Aux m) (u : UnselectedCoordinates σ) :
    selectedParameterLift σ v
      (t, parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z)) =
      ((t, v + selectedCoordinateSplit σ (0, u)), z) := by
  rw [add_assoc, ← selectedCoordinateSplit_eq_insertion]
  exact selectedParameterLift_split σ v t z u

theorem Family.timeSliceExtension_selected_eq_zero_of_notMem_chart {d : ℕ}
    (G : Family 2 d) (ψ : Cutoff d) (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2))
    (K : Set ((ℝ × Aux (d + 2)) × Aux 2)) (L : Set (ℝ × Parameters 2 d))
    (hLift : ∀ x ∈ L, selectedParameterLift σ v x ∈ K)
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ)
    (hcenter : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i),
      (b + (i : ℝ) * δ, x.2) ∈ L)
    (u : UnselectedCoordinates σ) (h : Plane → ℂ) (r : ℝ) {z : Aux 2}
    (hz : ((b + (i : ℝ) * δ, v + selectedCoordinateSplit σ (0, u)), z) ∉ K) :
    timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
      (fun x => (ψ (x.2.1, x.1) : ℂ)) h r (b + (i : ℝ) * δ) δ
      (parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z)) = 0 := by
  let p := parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z)
  have ht (t : ℝ) : ψ (t, p) * timePartitionWindow ((t - (b + (i : ℝ) * δ)) / δ) = 0 := by
    by_contra hn
    have he : ((t - (b + (i : ℝ) * δ)) / δ) = (t - b) / δ - (i : ℝ) := by
      field_simp
      ring
    have hx : (t, p) ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i) := by
      apply subset_closure
      change ψ (t, p) * timePartitionWindow ((t - b) / δ - (i : ℝ)) ≠ 0
      rw [← he]
      exact hn
    have hK := hLift _ (hcenter _ hx)
    rw [selectedParameterLift_frozen_selected σ v] at hK
    exact hz hK
  unfold timeSliceExtension
  apply integral_eq_zero_of_ae
  filter_upwards [] with η
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  have he : (ψ (t, p) : ℂ) * (timePartitionWindow ((t - (b + (i : ℝ) * δ)) / δ) : ℂ) = 0 := by
    exact_mod_cast ht t
  change _ * (ψ (t, p) : ℂ) * (timePartitionWindow ((t - (b + (i : ℝ) * δ)) / δ) : ℂ) * h (t, η) = 0
  rw [mul_assoc (_ : ℂ) (ψ (t, p) : ℂ)
    (timePartitionWindow ((t - (b + (i : ℝ) * δ)) / δ) : ℂ), he, mul_zero, zero_mul]

/-- The chart restriction in the nonlinear Jacobian estimate loses no
part of the original operator's selected-parameter mass. -/
theorem Family.lintegral_timeSliceExtension_selected_eq_restrict {d : ℕ}
    (G : Family 2 d) (ψ : Cutoff d) (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2))
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hK : IsCompact K)
    (L : Set (ℝ × Parameters 2 d))
    (hLift : ∀ x ∈ L, selectedParameterLift σ v x ∈ K)
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : ℕ)
    (hcenter : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i),
      (b + (i : ℝ) * δ, x.2) ∈ L)
    (u : UnselectedCoordinates σ) (h : Plane → ℂ) (r : ℝ) :
    (∫⁻ z : Aux 2, ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
      (fun x => (ψ (x.2.1, x.1) : ℂ)) h r (b + (i : ℝ) * δ) δ
      (parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) =
    ∫⁻ z in {z | ((b + (i : ℝ) * δ, v + selectedCoordinateSplit σ (0, u)), z) ∈ K},
      ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
      (fun x => (ψ (x.2.1, x.1) : ℂ)) h r (b + (i : ℝ) * δ) δ
      (parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ) := by
  let A : Set (Aux 2) :=
    {z | ((b + (i : ℝ) * δ, v + selectedCoordinateSplit σ (0, u)), z) ∈ K}
  have hA : MeasurableSet A := hK.isClosed.measurableSet.preimage
    (continuous_const.prodMk continuous_id).measurable
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ A
  · simp only [Set.indicator_of_mem hz]
  · have hzero := G.timeSliceExtension_selected_eq_zero_of_notMem_chart
      ψ σ v K L hLift b hδ i hcenter u h r hz
    simp only [Set.indicator_of_notMem hz, hzero, enorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

theorem Family.cutoffPartialExtension_selected_eq_zero_of_notMem_chart {d : ℕ}
    (G : Family 2 d) (ψ : Cutoff d) (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2))
    (K : Set ((ℝ × Aux (d + 2)) × Aux 2)) (L : Set (ℝ × Parameters 2 d))
    (hLift : ∀ x ∈ L, selectedParameterLift σ v x ∈ K)
    (b : ℝ) {δ : ℝ} (i : ℕ)
    (hcenter : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i),
      (b + (i : ℝ) * δ, x.2) ∈ L)
    (u : UnselectedCoordinates σ) (F : FrequencyCutoff) (βfreq : ℝ → ℝ)
    (f : Plane → ℂ) (r : ℝ) {z : Aux 2}
    (hz : ((b + (i : ℝ) * δ, v + selectedCoordinateSplit σ (0, u)), z) ∉ K) :
    G.cutoffPartialExtension (scaleTimeLocalizedCutoff ψ b δ i) F βfreq r f
      (parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z)) = 0 := by
  by_contra hn
  have hp := G.support_cutoffPartialExtension_time_piece ψ F βfreq b δ r i f L hcenter hn
  have hK := hLift _ hp
  rw [selectedParameterLift_frozen_selected σ v] at hK
  exact hz hK

theorem Family.lintegral_cutoffPartialExtension_selected_eq_restrict {d : ℕ}
    (G : Family 2 d) (ψ : Cutoff d) (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2))
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hK : IsCompact K)
    (L : Set (ℝ × Parameters 2 d))
    (hLift : ∀ x ∈ L, selectedParameterLift σ v x ∈ K)
    (b : ℝ) {δ : ℝ} (i : ℕ)
    (hcenter : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i),
      (b + (i : ℝ) * δ, x.2) ∈ L)
    (u : UnselectedCoordinates σ) (F : FrequencyCutoff) (βfreq : ℝ → ℝ)
    (f : Plane → ℂ) (r : ℝ) :
    (∫⁻ z : Aux 2,
      ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff ψ b δ i) F βfreq r f
      (parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) =
    ∫⁻ z in {z | ((b + (i : ℝ) * δ, v + selectedCoordinateSplit σ (0, u)), z) ∈ K},
      ‖G.cutoffPartialExtension (scaleTimeLocalizedCutoff ψ b δ i) F βfreq r f
      (parameterFrame d ((v + selectedCoordinateSplit σ (0, u)) + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ) := by
  let A : Set (Aux 2) :=
    {z | ((b + (i : ℝ) * δ, v + selectedCoordinateSplit σ (0, u)), z) ∈ K}
  have hA : MeasurableSet A := hK.isClosed.measurableSet.preimage
    (continuous_const.prodMk continuous_id).measurable
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ A
  · simp only [Set.indicator_of_mem hz]
  · have hzero := G.cutoffPartialExtension_selected_eq_zero_of_notMem_chart
      ψ σ v K L hLift b i hcenter u F βfreq f r hz
    simp only [Set.indicator_of_notMem hz, hzero, enorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

end PlanarNikodym
