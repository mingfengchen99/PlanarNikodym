import PlanarNikodym.Geometry.SelectedCoordinateSplit

/-! The actual selected/frozen original parameters lift exactly into the
joint chart, including variable time centers. -/
noncomputable section
namespace PlanarNikodym

theorem selectedParameterLift_split {d m : ℕ}
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2)) (t : ℝ)
    (z : Aux m) (u : UnselectedCoordinates σ) :
    selectedParameterLift σ v (t, parameterFrame d (v + selectedCoordinateSplit σ (z, u))) =
      ((t, v + selectedCoordinateSplit σ (0, u)), z) := by
  simp only [selectedParameterLift, ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel_left]

end PlanarNikodym
