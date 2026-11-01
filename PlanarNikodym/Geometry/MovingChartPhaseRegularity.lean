import PlanarNikodym.Geometry.MovingCinematicCoordinates

/-! The zeroth entry of the actual moving jet chart recovers the original
phase. Analyticity of the joint chart therefore supplies original-phase
regularity throughout its source, without an additional phase assumption. -/
noncomputable section
namespace PlanarNikodym

theorem Family.analyticAt_of_moving_linear_chart {d : ℕ} (G : Family 2 d)
    (hm : 2 ≤ d + 2) (σ : Fin 2 ↪ Fin (d + 2))
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (he : ∀ x, E x = (x.1, G.movingLowerJetMap hm σ x))
    {x : (ℝ × Aux (d + 2)) × Aux 2} (hE : AnalyticAt ℝ E x) :
    AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
      (x.1.1, parameterFrame d (x.1.2 + coordinateInsertion σ x.2)) := by
  let p : ℝ × Parameters 2 d :=
    (x.1.1, parameterFrame d (x.1.2 + coordinateInsertion σ x.2))
  let A : (ℝ × Parameters 2 d) → ((ℝ × Aux (d + 2)) × Aux 2) :=
    fun y => ((y.1, (parameterFrame d).symm y.2 - coordinateInsertion σ x.2), x.2)
  have hA : AnalyticAt ℝ A p := by
    exact (analyticAt_fst.prod
      (((parameterFrame d).symm.analyticAt _ |>.comp (f := Prod.snd) analyticAt_snd).sub
        analyticAt_const)).prod analyticAt_const
  have hp : A p = x := by
    simp only [A, p, ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel_right, Prod.mk.eta]
  have hEA : AnalyticAt ℝ E (A p) := hp.symm ▸ hE
  let L : (((ℝ × Aux (d + 2)) × Aux 2)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 2)).comp (ContinuousLinearMap.snd ℝ _ _)
  have hcomp : AnalyticAt ℝ (fun y => (E (A y)).2 0) p :=
    (L.analyticAt _).comp (f := fun y => E (A y)) (hEA.comp (f := A) hA)
  have heq : (fun y => (E (A y)).2 0) = fun y : ℝ × Parameters 2 d => G.γ y.1 y.2 := by
    funext y
    rw [he]
    simp only [A, Family.movingLowerJetMap, Family.lowerCinematicJetMap,
      Family.cinematicJetMap, timeDerivative, Fin.val_castLE, Fin.val_zero,
      sub_add_cancel, ContinuousLinearEquiv.apply_symm_apply]
  rw [heq] at hcomp
  exact hcomp

end PlanarNikodym
