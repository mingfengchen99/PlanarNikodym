import PlanarNikodym.Avoidance.AvoidanceJets
import PlanarNikodym.Geometry.LocalCoordinates

/-! The cinematic matrix is the actual Jacobian of the finite time-jet
map in the fixed parameter frame. Its determinant therefore supplies
genuine local analytic coordinates. -/
noncomputable section
open Set Filter
open scoped Topology Matrix

namespace PlanarNikodym

def Family.cinematicJetMap {d : ℕ} (G : Family 2 d) (t : ℝ)
    (v : Aux (d + 2)) : Aux (d + 2) :=
  fun i => timeDerivative (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2) i
    (t, parameterFrame d v)

theorem Family.cinematicJetMap_analyticAt {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v)) :
    AnalyticAt ℝ (G.cinematicJetMap t) v := by
  apply AnalyticAt.pi
  intro i
  exact (timeDerivative_analyticAt ha i).comp
    (f := fun w : Aux (d + 2) => (t, parameterFrame d w))
    (analyticAt_const.prod ((parameterFrame d).toContinuousLinearMap.analyticAt v))

/-- Equality of the coordinate entries follows from actual commutation
of analytic mixed derivatives and the chain rule for `parameterFrame`. -/
theorem Family.cinematicMatrix_eq_cinematicJetMap_coordinate_fderiv
    {d : ℕ} (G : Family 2 d) {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v)) (i j : Fin (d + 2)) :
    G.cinematicMatrix (t, parameterFrame d v) i j =
      fderiv ℝ (fun w => G.cinematicJetMap t w i) v (Pi.single j 1) := by
  let F : ℝ × Parameters 2 d → ℝ := fun x => G.γ x.1 x.2
  change timeDerivative (fun x => fderiv ℝ F x
    (0, parameterFrame d (Pi.single j 1))) i (t, parameterFrame d v) = _
  rw [ProjectionModel.timeDerivative_fderiv_apply ha]
  have hT := timeDerivative_analyticAt ha i
  have hslice : AnalyticAt ℝ
      (fun p : Parameters 2 d => timeDerivative F i (t, p)) (parameterFrame d v) :=
    hT.comp (f := fun p : Parameters 2 d => (t, p)) (analyticAt_const.prod analyticAt_id)
  have hchain : fderiv ℝ (fun w : Aux (d + 2) =>
      timeDerivative F i (t, parameterFrame d w)) v =
      (fderiv ℝ (fun p : Parameters 2 d => timeDerivative F i (t, p))
        (parameterFrame d v)).comp (parameterFrame d).toContinuousLinearMap :=
    (hslice.differentiableAt.hasFDerivAt.comp v
      (parameterFrame d).toContinuousLinearMap.hasFDerivAt).fderiv
  change fderiv ℝ (timeDerivative F i) (t, parameterFrame d v)
    (0, parameterFrame d (Pi.single j 1)) =
      fderiv ℝ (fun w : Aux (d + 2) => timeDerivative F i (t, parameterFrame d w)) v
        (Pi.single j 1)
  rw [hchain, fderiv_snd_slice (timeDerivative F i) (t, parameterFrame d v)
    hT.differentiableAt]
  rfl

/-- The standard-basis matrix of the actual finite-jet derivative is
exactly the previously defined cinematic matrix. -/
theorem Family.cinematicJetMap_fderiv_matrix {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v)) :
    LinearMap.toMatrix' (fderiv ℝ (G.cinematicJetMap t) v).toLinearMap =
      G.cinematicMatrix (t, parameterFrame d v) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  have he := fderiv_apply (G.cinematicJetMap_analyticAt ha).differentiableAt i
  calc
    (fderiv ℝ (G.cinematicJetMap t) v) (Pi.single j 1) i =
        fderiv ℝ (fun w => G.cinematicJetMap t w i) v (Pi.single j 1) :=
      (congrArg (fun L : Aux (d + 2) →L[ℝ] ℝ => L (Pi.single j 1)) he).symm
    _ = G.cinematicMatrix (t, parameterFrame d v) i j :=
      (G.cinematicMatrix_eq_cinematicJetMap_coordinate_fderiv ha i j).symm

/-- Nonzero cinematic determinant makes the actual parameter derivative
of the finite jet invertible. -/
theorem Family.cinematicJetMap_fderiv_isInvertible {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v))
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0) :
    (fderiv ℝ (G.cinematicJetMap t) v).IsInvertible := by
  apply isInvertible_of_det_coordinates
  change (LinearMap.toMatrix' (fderiv ℝ (G.cinematicJetMap t) v).toLinearMap).det ≠ 0
  rw [G.cinematicJetMap_fderiv_matrix ha]
  exact hdet

/-- At a nondegenerate analytic point, the genuine time jet gives an
analytic coordinate chart in any prescribed neighborhood of the parameter. -/
theorem Family.exists_cinematicJetMap_analytic_chart {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v))
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0)
    (U : Set (Aux (d + 2))) (hU : U ∈ 𝓝 v) :
    ∃ e : OpenPartialHomeomorph (Aux (d + 2)) (Aux (d + 2)),
      v ∈ e.source ∧ e.source ⊆ U ∧ (∀ w, e w = G.cinematicJetMap t w) ∧
        AnalyticOnNhd ℝ e e.source ∧ AnalyticOnNhd ℝ e.symm e.target :=
  exists_analytic_chart (G.cinematicJetMap t) v
    (G.cinematicJetMap_analyticAt ha) (G.cinematicJetMap_fderiv_isInvertible ha hdet) U hU

end PlanarNikodym
