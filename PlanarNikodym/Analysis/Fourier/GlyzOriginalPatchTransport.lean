import PlanarNikodym.Analysis.Fourier.GlyzFrozenPatchAssembly

/-! Full-dimensional chart patches retain the original output measure.
The smaller atlas cutoff is controlled by the cutoff in the actual
single-chart estimate, and every child returns to the original norm. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

theorem glyz_original_frozen_patch_power_le {d : ℕ}
    (σ : Fin (d + 2) ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (d + 2))
      ((ℝ × Aux (d + 2)) × Aux (d + 2)))
    (he : ∀ x, (e x).1 = x.1)
    (ψ : Cutoff d) (hψ : Continuous ψ) (hψrange : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (ρ : ((ℝ × Aux (d + 2)) × Aux (d + 2)) → ℝ)
    (K : Set ((ℝ × Aux (d + 2)) × Aux (d + 2))) (hKS : K ⊆ e.source)
    (hs : ∀ x ∈ tsupport ψ, selectedParameterLift σ v x ∈ K)
    (hρ : ∀ x ∈ K, ρ (e x) = 1)
    (F : Parameters 2 d → ℂ) (hF : Continuous F) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖(ψ (c, x) : ℂ) * F x‖ₑ ^ p) ≤
      ∫⁻ z in {z | ((c, v), z) ∈ e.source},
        ‖(ρ ((c, v), (e ((c, v), z)).2) : ℂ) *
          F (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ p := by
  have hc : Continuous (fun x => ψ (c, x)) := hψ.comp (continuous_const.prodMk continuous_id)
  have hm : Measurable (fun x => ‖(ψ (c, x) : ℂ) * F x‖ₑ ^ p) :=
    ((Complex.continuous_ofReal.comp hc).mul hF).measurable.enorm.pow_const p
  rw [glyz_lintegral_original_full_parameters σ v _ hm]
  apply glyz_output_patch_dominated_in_chart volume
    (fun z => ψ (c, parameterFrame d (v + coordinateInsertion σ z)))
    (fun z => ρ ((c, v), (e ((c, v), z)).2))
    (fun z => F (parameterFrame d (v + coordinateInsertion σ z)))
    {z | ((c, v), z) ∈ e.source}
    (fun z => hψrange _) ?_ ?_ hp
  · intro z hz
    have hh := hs (c, parameterFrame d (v + coordinateInsertion σ z)) (subset_tsupport _ hz)
    rw [glyz_selectedParameterLift_on_fiber] at hh
    exact hKS hh
  · intro z hz
    have hh := hs (c, parameterFrame d (v + coordinateInsertion σ z)) (subset_tsupport _ hz)
    rw [glyz_selectedParameterLift_on_fiber] at hh
    have heq : ((c, v), (e ((c, v), z)).2) = e ((c, v), z) :=
      Prod.ext (he ((c, v), z)).symm rfl
    rw [heq]
    exact hρ _ hh

theorem glyz_original_chart_child_power_le {d : ℕ}
    (σ : Fin (d + 2) ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (d + 2))
      ((ℝ × Aux (d + 2)) × Aux (d + 2)))
    (ρ : ((ℝ × Aux (d + 2)) × Aux (d + 2)) → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1)
    (F : Parameters 2 d → ℂ) (hF : Continuous F) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ z in {z | ((c, v), z) ∈ e.source},
      ‖(ρ ((c, v), (e ((c, v), z)).2) : ℂ) *
        F (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ p) ≤
      ∫⁻ x, ‖F x‖ₑ ^ p := by
  calc
    _ ≤ ∫⁻ z, ‖(ρ ((c, v), (e ((c, v), z)).2) : ℂ) *
        F (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ p :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ∫⁻ z, ‖F (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ p :=
      glyz_output_cutoff_power_le volume _ _ (fun z => hρ _) hp
    _ = _ := (glyz_lintegral_original_full_parameters σ v _ (hF.measurable.enorm.pow_const p)).symm

end PlanarNikodym
