import PlanarNikodym.Geometry.CinematicLowerMinors
import Mathlib.MeasureTheory.Function.Jacobian

/-! The selected lower cinematic minor gives genuine analytic coordinates
on a slice along the selected original parameter axes. -/

noncomputable section
open Set Filter
open scoped Topology Matrix

namespace PlanarNikodym

def coordinateInsertion {m N : ℕ} (σ : Fin m ↪ Fin N) :
    (Fin m → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ((Pi.basisFun ℝ (Fin m)).constr ℝ (fun i => Pi.single (σ i) 1)).toContinuousLinearMap

@[simp] theorem coordinateInsertion_single {m N : ℕ} (σ : Fin m ↪ Fin N) (j : Fin m) :
    coordinateInsertion σ (Pi.single j 1) = Pi.single (σ j) 1 := by
  change ((Pi.basisFun ℝ (Fin m)).constr ℝ (fun i => Pi.single (σ i) 1)) (Pi.single j 1) = _
  simpa only [Pi.basisFun_apply] using
    (Pi.basisFun ℝ (Fin m)).constr_basis ℝ (fun i => Pi.single (σ i) 1) j

def Family.lowerCinematicJetMap {d m : ℕ} (G : Family 2 d) (hm : m ≤ d + 2)
    (σ : Fin m ↪ Fin (d + 2)) (t : ℝ) (v : Aux (d + 2)) (z : Aux m) : Aux m :=
  fun i => G.cinematicJetMap t (v + coordinateInsertion σ z) (Fin.castLE hm i)

theorem Family.lowerCinematicJetMap_analyticAt_zero {d m : ℕ} (G : Family 2 d)
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2)) {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v)) :
    AnalyticAt ℝ (G.lowerCinematicJetMap hm σ t v) 0 := by
  have harg : AnalyticAt ℝ (fun z : Aux m => v + coordinateInsertion σ z) 0 :=
    analyticAt_const.add ((coordinateInsertion σ).analyticAt _)
  have hj : AnalyticAt ℝ (G.cinematicJetMap t) (v + coordinateInsertion σ 0) := by
    simpa only [map_zero, add_zero] using G.cinematicJetMap_analyticAt ha
  have hcomp : AnalyticAt ℝ (fun z : Aux m =>
      G.cinematicJetMap t (v + coordinateInsertion σ z)) 0 :=
    hj.comp (f := fun z : Aux m => v + coordinateInsertion σ z) harg
  apply AnalyticAt.pi
  intro i
  exact ((ContinuousLinearMap.proj (Fin.castLE hm i) : Aux (d + 2) →L[ℝ] ℝ).analyticAt _).comp hcomp

/-- The Jacobian of the actual sliced time-jet map is the selected
coordinate minor of the original cinematic matrix. -/
theorem Family.lowerCinematicJetMap_fderiv_matrix {d m : ℕ} (G : Family 2 d)
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2)) {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v)) :
    LinearMap.toMatrix' (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).toLinearMap =
      fun i j => G.cinematicMatrix (t, parameterFrame d v) (Fin.castLE hm i) (σ j) := by
  have hl := (G.lowerCinematicJetMap_analyticAt_zero hm σ ha).differentiableAt
  ext i j
  rw [LinearMap.toMatrix'_apply]
  have hfull : AnalyticAt ℝ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) v :=
    ((ContinuousLinearMap.proj (Fin.castLE hm i) : Aux (d + 2) →L[ℝ] ℝ).analyticAt _).comp
      (G.cinematicJetMap_analyticAt ha)
  have hd : HasFDerivAt (fun w => G.cinematicJetMap t w (Fin.castLE hm i))
      (fderiv ℝ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) v)
      (v + coordinateInsertion σ 0) := by
    simpa only [map_zero, add_zero] using hfull.differentiableAt.hasFDerivAt
  have hchain := (hd.comp 0 ((coordinateInsertion σ).hasFDerivAt.const_add v)).fderiv
  dsimp only [Function.comp_def] at hchain
  have he := fderiv_apply hl i
  calc
    (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0) (Pi.single j 1) i =
        fderiv ℝ (fun z => G.lowerCinematicJetMap hm σ t v z i) 0 (Pi.single j 1) :=
      (congrArg (fun L : Aux m →L[ℝ] ℝ => L (Pi.single j 1)) he).symm
    _ = fderiv ℝ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) v
        (Pi.single (σ j) 1) := by
      change fderiv ℝ (fun z => G.cinematicJetMap t (v + coordinateInsertion σ z)
        (Fin.castLE hm i)) 0 (Pi.single j 1) = _
      rw [hchain]
      change (fderiv ℝ (fun w => G.cinematicJetMap t w (Fin.castLE hm i)) v)
        (coordinateInsertion σ (Pi.single j 1)) = _
      rw [coordinateInsertion_single]
    _ = G.cinematicMatrix (t, parameterFrame d v) (Fin.castLE hm i) (σ j) :=
      (G.cinematicMatrix_eq_cinematicJetMap_coordinate_fderiv ha (Fin.castLE hm i) (σ j)).symm

/-- Nonzero full cinematic determinant supplies a selected lower slice
and an actual analytic local inverse, inside any prescribed neighborhood
of the slice origin. -/
theorem Family.exists_lowerCinematicJetMap_analytic_chart {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v))
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0) (m : ℕ) (hm : m ≤ d + 2)
    (U : Set (Aux m)) (hU : U ∈ 𝓝 (0 : Aux m)) :
    ∃ (σ : Fin m ↪ Fin (d + 2)) (e : OpenPartialHomeomorph (Aux m) (Aux m)),
      (0 : Aux m) ∈ e.source ∧ e.source ⊆ U ∧
      (∀ z, e z = G.lowerCinematicJetMap hm σ t v z) ∧
      AnalyticOnNhd ℝ e e.source ∧ AnalyticOnNhd ℝ e.symm e.target := by
  obtain ⟨σ, hσ⟩ := G.exists_cinematicInitialMinor hdet m hm
  have hinv : (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).IsInvertible := by
    apply isInvertible_of_det_coordinates
    change (LinearMap.toMatrix' (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).toLinearMap).det ≠ 0
    rw [G.lowerCinematicJetMap_fderiv_matrix hm σ ha]
    exact hσ
  obtain ⟨e, he0, heU, he, hea, hei⟩ := exists_analytic_chart
    (G.lowerCinematicJetMap hm σ t v) 0
    (G.lowerCinematicJetMap_analyticAt_zero hm σ ha) hinv U hU
  exact ⟨σ, e, he0, heU, he, hea, hei⟩

theorem Family.det_lowerCinematicJetMap_fderiv_zero {d m : ℕ} (G : Family 2 d)
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2)) {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v)) :
    LinearMap.det (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).toLinearMap =
      G.cinematicInitialMinor hm σ (t, parameterFrame d v) := by
  rw [← LinearMap.det_toMatrix', G.lowerCinematicJetMap_fderiv_matrix hm σ ha]
  rfl

/-- The chosen slice chart can keep the original phase analytic at
every point of its source, as well as keeping both chart maps analytic. -/
theorem Family.exists_regular_lowerCinematicJetMap_chart {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v))
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0) (m : ℕ) (hm : m ≤ d + 2)
    (U : Set (Aux m)) (hU : U ∈ 𝓝 (0 : Aux m)) :
    ∃ (σ : Fin m ↪ Fin (d + 2)) (e : OpenPartialHomeomorph (Aux m) (Aux m)),
      (0 : Aux m) ∈ e.source ∧ e.source ⊆ U ∧
      (∀ z, e z = G.lowerCinematicJetMap hm σ t v z) ∧
      AnalyticOnNhd ℝ e e.source ∧ AnalyticOnNhd ℝ e.symm e.target ∧
      ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
        (t, parameterFrame d (v + coordinateInsertion σ z)) := by
  obtain ⟨σ, hσ⟩ := G.exists_cinematicInitialMinor hdet m hm
  let S : Set (Aux m) := {z | AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
    (t, parameterFrame d (v + coordinateInsertion σ z))}
  have hmap : Continuous (fun z : Aux m =>
      (t, parameterFrame d (v + coordinateInsertion σ z))) :=
    continuous_const.prodMk ((parameterFrame d).continuous.comp
      (continuous_const.add (coordinateInsertion σ).continuous))
  have hopen : IsOpen {x : ℝ × Parameters 2 d |
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x} := isOpen_analyticAt ℝ _
  have hS : IsOpen S := hopen.preimage hmap
  have h0S : (0 : Aux m) ∈ S := by
    simpa only [S, mem_setOf_eq, map_zero, add_zero] using ha
  have hinv : (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).IsInvertible := by
    apply isInvertible_of_det_coordinates
    change (LinearMap.toMatrix' (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).toLinearMap).det ≠ 0
    rw [G.lowerCinematicJetMap_fderiv_matrix hm σ ha]
    exact hσ
  obtain ⟨e, he0, heUS, he, hea, hei⟩ := exists_analytic_chart
    (G.lowerCinematicJetMap hm σ t v) 0
    (G.lowerCinematicJetMap_analyticAt_zero hm σ ha) hinv (U ∩ S) (inter_mem hU (hS.mem_nhds h0S))
  exact ⟨σ, e, he0, fun z hz => (heUS hz).1, he, hea, hei, fun z hz => (heUS hz).2⟩

/-- The analytic local inverses constructed above support the actual
Lebesgue Jacobian change of variables, for arbitrary complex integrands. -/
theorem integral_analytic_chart_target {m : ℕ} (e : OpenPartialHomeomorph (Aux m) (Aux m))
    (he : AnalyticOnNhd ℝ e e.source) (F : Aux m → ℂ) :
    (∫ y in e.target, F y) = ∫ z in e.source,
      |LinearMap.det (fderiv ℝ e z).toLinearMap| • F (e z) := by
  exact MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul MeasureTheory.volume
    (fun z hz => (he z hz).differentiableAt.hasFDerivAt) F

end PlanarNikodym
