import PlanarNikodym.Analysis.Localization.MovingChartPartition

/-! The regular-segment guard supplied by the constructed time partition
applies exactly where the real cutoff amplitude is active. This turns
the finite geometric localization into the center/endpoint guards needed
for the original phase's Taylor-amplitude extension. -/
noncomputable section
open Set
namespace PlanarNikodym

theorem active_timeSlice_center_endpoints {P : Type} [TopologicalSpace P]
    (ψ : ℝ × P → ℝ) (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ)
    (L : Set (ℝ × P))
    (hspan : ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ j),
      ∀ τ ∈ Icc (-1 : ℝ) 1,
        ∀ s ∈ uIcc (b + (j : ℝ) * δ) (b + (j : ℝ) * δ + δ * τ), (s, x.2) ∈ L)
    (p : P) (τ : ℝ)
    (hactive : (ψ (b + (j : ℝ) * δ + δ * τ, p) : ℂ) * (timePartitionWindow τ : ℂ) ≠ 0) :
    (b + (j : ℝ) * δ, p) ∈ L ∧ (b + (j : ℝ) * δ + δ * τ, p) ∈ L := by
  have hψ : ψ (b + (j : ℝ) * δ + δ * τ, p) ≠ 0 := by
    intro hz
    exact hactive (by rw [hz, Complex.ofReal_zero, zero_mul])
  have hw : timePartitionWindow τ ≠ 0 := by
    intro hz
    exact hactive (by rw [hz, Complex.ofReal_zero, mul_zero])
  have hτ : τ ∈ Icc (-1 : ℝ) 1 := tsupport_timePartitionWindow_subset (subset_closure hw)
  have he : ((b + (j : ℝ) * δ + δ * τ - b) / δ - (j : ℝ)) = τ := by
    field_simp
    ring
  have hx : (b + (j : ℝ) * δ + δ * τ, p) ∈
      tsupport (scaleTimeLocalizedCutoff ψ b δ j) := by
    apply subset_closure
    change ψ (b + (j : ℝ) * δ + δ * τ, p) *
      timePartitionWindow ((b + (j : ℝ) * δ + δ * τ - b) / δ - (j : ℝ)) ≠ 0
    rw [he]
    exact mul_ne_zero hψ hw
  exact ⟨hspan _ hx τ hτ _ left_mem_uIcc, hspan _ hx τ hτ _ right_mem_uIcc⟩

end PlanarNikodym
