import PlanarNikodym.Geometry.ParameterLebesgueCoordinates

/-! The full selected coordinate frame is an actual permutation,
with no unused-coordinate integral or measure factor. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

def glyzFullCoordinateEquiv {m : ℕ} (σ : Fin m ↪ Fin m) : Aux m ≃L[ℝ] Aux m :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin m => ℝ)
    (Equiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩)

theorem glyzFullCoordinateEquiv_eq_insertion {m : ℕ} (σ : Fin m ↪ Fin m) :
    (glyzFullCoordinateEquiv σ).toContinuousLinearMap = coordinateInsertion σ := by
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.ext
  have he : (glyzFullCoordinateEquiv σ).toLinearMap = (coordinateInsertion σ).toLinearMap := by
    apply (Pi.basisFun ℝ (Fin m)).ext
    intro j
    simp only [Pi.basisFun_apply]
    change glyzFullCoordinateEquiv σ (Pi.single j 1) = coordinateInsertion σ (Pi.single j 1)
    rw [coordinateInsertion_single]
    ext i
    obtain ⟨l, rfl⟩ := Finite.surjective_of_injective σ.injective i
    let e : Fin m ≃ Fin m := Equiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
    change Equiv.piCongrLeft (fun _ : Fin m => ℝ) e (Pi.single j 1) (e l) = _
    rw [Equiv.piCongrLeft_apply_apply]
    simp only [Pi.single_apply, σ.injective.eq_iff]
  intro x
  exact congrArg (fun L : Aux m →ₗ[ℝ] Aux m => L x) he

theorem glyzFullCoordinateEquiv_volume_preserving {m : ℕ} (σ : Fin m ↪ Fin m) :
    MeasurePreserving (glyzFullCoordinateEquiv σ) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) _

theorem glyz_lintegral_original_full_parameters {d : ℕ}
    (σ : Fin (d + 2) ↪ Fin (d + 2)) (v : Aux (d + 2))
    (F : Parameters 2 d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ z, F (parameterFrame d (v + coordinateInsertion σ z)) := by
  rw [← (parameterFrame_volume_preserving d).lintegral_comp hF,
    ← lintegral_add_left_eq_self (fun w => F (parameterFrame d w)) v]
  have hm : Measurable (fun w => F (parameterFrame d (v + w))) :=
    hF.comp ((parameterFrame d).continuous.comp (continuous_const.add continuous_id)).measurable
  rw [← (glyzFullCoordinateEquiv_volume_preserving σ).lintegral_comp hm]
  congr 1
  funext z
  have he := congrArg (fun L : Aux (d + 2) →L[ℝ] Aux (d + 2) => L z)
    (glyzFullCoordinateEquiv_eq_insertion σ)
  exact congrArg (fun w => F (parameterFrame d (v + w))) he

/-- On each chosen fiber, the frozen parameter is precisely the chart
base point, including for a full-coordinate chart. -/
theorem glyz_selectedParameterLift_on_fiber {d m : ℕ}
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ) (z : Aux m) :
    selectedParameterLift σ v (c, parameterFrame d (v + coordinateInsertion σ z)) = ((c, v), z) := by
  have hs : selectedCoordinateSplit σ (z, 0) = coordinateInsertion σ z := by
    rw [selectedCoordinateSplit_eq_insertion]
    have hz : selectedCoordinateSplit σ (0, 0) = 0 := map_zero _
    rw [hz, zero_add]
  simp only [selectedParameterLift, ContinuousLinearEquiv.symm_apply_apply,
    add_sub_cancel_left, ← hs]
  have hz : selectedCoordinateSplit σ (0, 0) = 0 := map_zero _
  rw [hz, add_zero]

end PlanarNikodym
