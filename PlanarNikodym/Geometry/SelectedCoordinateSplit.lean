import PlanarNikodym.Geometry.CinematicLowerCoordinates
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! Selected parameter axes and their actual complement, with Lebesgue
measure preserved. The complement remains available for Tonelli/Fubini. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

abbrev UnselectedCoordinates {m N : ℕ} (σ : Fin m ↪ Fin N) :=
  ↥((Set.range σ)ᶜ : Set (Fin N)) → ℝ

def selectedIndexEquiv {m N : ℕ} (σ : Fin m ↪ Fin N) :
    Fin m ⊕ ↥((Set.range σ)ᶜ : Set (Fin N)) ≃ Fin N :=
  (Equiv.sumCongr (Equiv.ofInjective σ σ.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range σ))

def selectedCoordinateSplit {m N : ℕ} (σ : Fin m ↪ Fin N) :
    (Aux m × UnselectedCoordinates σ) ≃L[ℝ] Aux N :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin m) _ (fun _ => ℝ)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin N => ℝ) (selectedIndexEquiv σ))

theorem selectedCoordinateSplit_volume_preserving {m N : ℕ} (σ : Fin m ↪ Fin N) :
    MeasurePreserving (selectedCoordinateSplit σ) volume volume := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) (selectedIndexEquiv σ)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ => ℝ))

theorem selectedCoordinateSplit_single {m N : ℕ} (σ : Fin m ↪ Fin N) (j : Fin m) :
    selectedCoordinateSplit σ (Pi.single j 1, 0) = Pi.single (σ j) 1 := by
  classical
  ext i
  obtain ⟨i, rfl⟩ := (selectedIndexEquiv σ).surjective i
  change (Equiv.piCongrLeft (fun _ : Fin N => ℝ) (selectedIndexEquiv σ)
    ((Equiv.sumPiEquivProdPi (fun _ => ℝ)).symm (Pi.single j 1, 0)))
      (selectedIndexEquiv σ i) = _
  rw [Equiv.piCongrLeft_apply_apply]
  have hinj := (selectedIndexEquiv σ).injective
  have hj : selectedIndexEquiv σ (Sum.inl j) = σ j := rfl
  rw [← hj]
  cases i with
  | inl k => simp [Equiv.sumPiEquivProdPi, Pi.single_apply, hinj.eq_iff]
  | inr k => simp [Equiv.sumPiEquivProdPi, hinj.eq_iff]

theorem selectedCoordinateSplit_eq_insertion {m N : ℕ} (σ : Fin m ↪ Fin N)
    (z : Aux m) (u : UnselectedCoordinates σ) :
    selectedCoordinateSplit σ (z, u) =
      selectedCoordinateSplit σ (0, u) + coordinateInsertion σ z := by
  have hL : (selectedCoordinateSplit σ).toLinearMap.comp (LinearMap.inl ℝ _ _) =
      (coordinateInsertion σ).toLinearMap := by
    apply (Pi.basisFun ℝ (Fin m)).ext
    intro j
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.inl_apply]
    change selectedCoordinateSplit σ (Pi.single j 1, 0) = coordinateInsertion σ (Pi.single j 1)
    rw [selectedCoordinateSplit_single, coordinateInsertion_single]
  have hz := congrArg (fun L : Aux m →ₗ[ℝ] Aux N => L z) hL
  change selectedCoordinateSplit σ (z, 0) = coordinateInsertion σ z at hz
  rw [← hz, ← map_add]
  simp

/-- An exact separation of selected and unselected original coordinates,
for arbitrary nonnegative measurable integrands, including infinite norms. -/
theorem lintegral_selectedCoordinateSplit {m N : ℕ} (σ : Fin m ↪ Fin N)
    (F : Aux N → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v) = ∫⁻ z : Aux m, ∫⁻ u : UnselectedCoordinates σ,
      F (selectedCoordinateSplit σ (z, u)) := by
  rw [← (selectedCoordinateSplit_volume_preserving σ).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp (selectedCoordinateSplit σ).continuous.measurable).aemeasurable

def selectedParameterLift {d m : ℕ} (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2))
    (x : ℝ × Parameters 2 d) : (ℝ × Aux (d + 2)) × Aux m :=
  let w := (selectedCoordinateSplit σ).symm ((parameterFrame d).symm x.2 - v)
  ((x.1, v + selectedCoordinateSplit σ (0, w.2)), w.1)

theorem continuous_selectedParameterLift {d m : ℕ} (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2)) :
    Continuous (selectedParameterLift σ v) := by
  unfold selectedParameterLift
  fun_prop

theorem selectedParameterLift_self {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) (t : ℝ) :
    selectedParameterLift σ v (t, parameterFrame d v) = ((t, v), 0) := by
  simp [selectedParameterLift]

/-- The lift separates selected and frozen parameters without changing
the actual original parameter point. -/
theorem selectedParameterLift_reconstruct {d m : ℕ} (σ : Fin m ↪ Fin (d + 2))
    (v : Aux (d + 2)) (x : ℝ × Parameters 2 d) :
    parameterFrame d ((selectedParameterLift σ v x).1.2 +
      coordinateInsertion σ (selectedParameterLift σ v x).2) = x.2 := by
  let w := (selectedCoordinateSplit σ).symm ((parameterFrame d).symm x.2 - v)
  change parameterFrame d (v + selectedCoordinateSplit σ (0, w.2) + coordinateInsertion σ w.1) = _
  rw [add_assoc, ← selectedCoordinateSplit_eq_insertion]
  change parameterFrame d (v + selectedCoordinateSplit σ w) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel, ContinuousLinearEquiv.apply_symm_apply]

end PlanarNikodym
