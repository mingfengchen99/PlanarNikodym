import PlanarNikodym.Analysis.Fourier.GlyzOriginalPatchTransport

/-! Lower-dimensional selected fibers preserve the original output
measure. The unused-coordinate error is integrated only over a fixed
compact projection of the atlas patch. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace PlanarNikodym

def glyzFiberBase {d m : ℕ} (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2))
    (u : UnselectedCoordinates σ) : Aux (d + 2) :=
  v + selectedCoordinateSplit σ (0, u)

def glyzFiberParameter {d m : ℕ} (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2))
    (u : UnselectedCoordinates σ) (z : Aux m) : Parameters 2 d :=
  parameterFrame d (glyzFiberBase σ v u + coordinateInsertion σ z)

def glyzFiberProjection {d m : ℕ} (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2))
    (x : ℝ × Parameters 2 d) : UnselectedCoordinates σ :=
  ((selectedCoordinateSplit σ).symm ((parameterFrame d).symm x.2 - v)).2

theorem glyzFiberParameter_eq_split {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) (u : UnselectedCoordinates σ) (z : Aux m) :
    glyzFiberParameter σ v u z = parameterFrame d (v + selectedCoordinateSplit σ (z, u)) := by
  unfold glyzFiberParameter glyzFiberBase
  rw [add_assoc, ← selectedCoordinateSplit_eq_insertion]

theorem continuous_glyzFiberParameter {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) : Continuous (fun uz : UnselectedCoordinates σ × Aux m =>
      glyzFiberParameter σ v uz.1 uz.2) := by
  simp only [glyzFiberParameter_eq_split]
  fun_prop

theorem continuous_glyzFiberProjection {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) : Continuous (glyzFiberProjection σ v) := by
  unfold glyzFiberProjection
  fun_prop

theorem glyzFiberProjection_fiber {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (u : UnselectedCoordinates σ) (z : Aux m) :
    glyzFiberProjection σ v (c, glyzFiberParameter σ v u z) = u := by
  simp only [glyzFiberProjection, glyzFiberParameter_eq_split,
    ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel_left]

theorem glyz_selectedParameterLift_fiber {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) (c : ℝ) (u : UnselectedCoordinates σ) (z : Aux m) :
    selectedParameterLift σ v (c, glyzFiberParameter σ v u z) =
      ((c, glyzFiberBase σ v u), z) := by
  simp only [selectedParameterLift, glyzFiberParameter_eq_split,
    ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel_left, glyzFiberBase]

theorem glyz_lintegral_original_fibers {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) (F : Parameters 2 d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ u : UnselectedCoordinates σ, ∫⁻ z : Aux m,
      F (glyzFiberParameter σ v u z) := by
  simpa only [glyzFiberParameter_eq_split] using lintegral_original_selected_parameters σ v F hF

/-- The cutoff in the actual lower-degree chart dominates the frozen
atlas patch on each unused-coordinate fiber. -/
theorem glyz_original_fiber_patch_power_le {d m : ℕ}
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (u : UnselectedCoordinates σ)
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
      ((ℝ × Aux (d + 2)) × Aux m))
    (he : ∀ x, (e x).1 = x.1)
    (ψ : Cutoff d) (hψrange : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (ρ : ((ℝ × Aux (d + 2)) × Aux m) → ℝ)
    (K : Set ((ℝ × Aux (d + 2)) × Aux m)) (hKS : K ⊆ e.source)
    (hs : ∀ x ∈ tsupport ψ, selectedParameterLift σ v x ∈ K)
    (hρ : ∀ x ∈ K, ρ (e x) = 1)
    (F : Parameters 2 d → ℂ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ z, ‖(ψ (c, glyzFiberParameter σ v u z) : ℂ) *
      F (glyzFiberParameter σ v u z)‖ₑ ^ p) ≤
      ∫⁻ z in {z | ((c, glyzFiberBase σ v u), z) ∈ e.source},
        ‖(ρ ((c, glyzFiberBase σ v u), (e ((c, glyzFiberBase σ v u), z)).2) : ℂ) *
          F (glyzFiberParameter σ v u z)‖ₑ ^ p := by
  apply glyz_output_patch_dominated_in_chart volume _ _ _ _
    (fun z => hψrange _) ?_ ?_ hp
  · intro z hz
    have hh := hs (c, glyzFiberParameter σ v u z) (subset_tsupport _ hz)
    rw [glyz_selectedParameterLift_fiber] at hh
    exact hKS hh
  · intro z hz
    have hh := hs (c, glyzFiberParameter σ v u z) (subset_tsupport _ hz)
    rw [glyz_selectedParameterLift_fiber] at hh
    have heq : ((c, glyzFiberBase σ v u), (e ((c, glyzFiberBase σ v u), z)).2) =
        e ((c, glyzFiberBase σ v u), z) :=
      Prod.ext (he ((c, glyzFiberBase σ v u), z)).symm rfl
    rw [heq]
    exact hρ _ hh

theorem glyz_original_fiber_child_power_le {d m : ℕ}
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (u : UnselectedCoordinates σ)
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
      ((ℝ × Aux (d + 2)) × Aux m))
    (ρ : ((ℝ × Aux (d + 2)) × Aux m) → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1)
    (F : Parameters 2 d → ℂ) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ z in {z | ((c, glyzFiberBase σ v u), z) ∈ e.source},
      ‖(ρ ((c, glyzFiberBase σ v u), (e ((c, glyzFiberBase σ v u), z)).2) : ℂ) *
        F (glyzFiberParameter σ v u z)‖ₑ ^ p) ≤
      ∫⁻ z, ‖F (glyzFiberParameter σ v u z)‖ₑ ^ p := by
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    (glyz_output_cutoff_power_le volume _ _ (fun z => hρ _) hp)

end PlanarNikodym
