import PlanarNikodym.Geometry.SelectedCoordinateSplit

/-! The actual parameter frame is a Lebesgue-preserving coordinate
reordering. Selected/unselected separation therefore applies to the
original parameter integral, including translated local charts. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace PlanarNikodym

theorem parameterFrame_volume_preserving (d : ℕ) :
    MeasurePreserving (parameterFrame d) volume volume := by
  let I : Fin 2 ⊕ Fin d ≃ Fin (d + 2) := finSumFinEquiv.trans (finCongr (Nat.add_comm 2 d))
  let f : Aux (d + 2) → Parameters 2 d :=
    fun v => Equiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin d => ℝ)
      (Equiv.piCongrLeft (fun _ => ℝ) I.symm v)
  have hf : MeasurePreserving f volume volume :=
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin d => ℝ)).comp
      (volume_measurePreserving_piCongrLeft (fun _ : Fin 2 ⊕ Fin d => ℝ) I.symm)
  have heq : f = parameterFrame d := by
    funext v
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · ext i
      change (Equiv.piCongrLeft (fun _ => ℝ) I.symm v) (Sum.inr i) = v i.succ.succ
      rw [Equiv.piCongrLeft_apply]
      simp only [Equiv.symm_symm, eq_rec_constant]
      congr 1
      apply Fin.ext
      simp [I, Nat.add_comm]
      omega
  rwa [heq] at hf

/-- Tonelli in the original parameter measure, with the unselected
parameters on the outside. The selected slice has its true coordinates
and no untracked measure-normalization constant. -/
theorem lintegral_original_selected_parameters {d m : ℕ}
    (σ : Fin m ↪ Fin (d + 2)) (v : Aux (d + 2))
    (F : Parameters 2 d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F q) = ∫⁻ u : UnselectedCoordinates σ, ∫⁻ z : Aux m,
      F (parameterFrame d (v + selectedCoordinateSplit σ (z, u))) := by
  rw [← (parameterFrame_volume_preserving d).lintegral_comp hF]
  rw [← lintegral_add_left_eq_self (fun w => F (parameterFrame d w)) v]
  let A := (Homeomorph.prodComm _ _).trans (selectedCoordinateSplit σ).toHomeomorph
  have hA : MeasurePreserving A volume volume :=
    (selectedCoordinateSplit_volume_preserving σ).comp Measure.measurePreserving_swap
  have hG : Measurable (fun w => F (parameterFrame d (v + w))) :=
    hF.comp ((parameterFrame d).continuous.comp (continuous_const.add continuous_id)).measurable
  rw [← hA.lintegral_comp hG]
  exact lintegral_prod _ (hG.comp A.continuous.measurable).aemeasurable

end PlanarNikodym
