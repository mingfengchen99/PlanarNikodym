import PlanarNikodym.Geometry.ParametricAnalyticCoordinates
import PlanarNikodym.Geometry.CinematicLowerCoordinates

/-! Joint analytic lower jet coordinates with both the Taylor center and
the unselected parameter values retained. -/
noncomputable section
open Set Filter
open scoped Topology
namespace PlanarNikodym

def Family.movingLowerJetMap {d m : ℕ} (G : Family 2 d) (hm : m ≤ d + 2)
    (σ : Fin m ↪ Fin (d + 2)) (x : (ℝ × Aux (d + 2)) × Aux m) : Aux m :=
  G.lowerCinematicJetMap hm σ x.1.1 x.1.2 x.2

theorem Family.movingLowerJetMap_analyticAt {d m : ℕ} (G : Family 2 d)
    (hm : m ≤ d + 2) (σ : Fin m ↪ Fin (d + 2))
    {x : (ℝ × Aux (d + 2)) × Aux m}
    (ha : AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
      (x.1.1, parameterFrame d (x.1.2 + coordinateInsertion σ x.2))) :
    AnalyticAt ℝ (G.movingLowerJetMap hm σ) x := by
  have harg : AnalyticAt ℝ (fun y : (ℝ × Aux (d + 2)) × Aux m =>
      (y.1.1, parameterFrame d (y.1.2 + coordinateInsertion σ y.2))) x := by
    have ht := ((ContinuousLinearMap.fst ℝ ℝ (Aux (d + 2))).analyticAt _).comp
      (f := Prod.fst) (analyticAt_fst (p := x))
    have hv := ((ContinuousLinearMap.snd ℝ ℝ (Aux (d + 2))).analyticAt _).comp
      (f := Prod.fst) (analyticAt_fst (p := x))
    exact ht.prod ((parameterFrame d).analyticAt _ |>.comp
      (f := fun y : (ℝ × Aux (d + 2)) × Aux m => y.1.2 + coordinateInsertion σ y.2)
      (hv.add ((coordinateInsertion σ).analyticAt _ |>.comp
        (f := Prod.snd) analyticAt_snd)))
  apply AnalyticAt.pi
  intro i
  exact (timeDerivative_analyticAt ha (Fin.castLE hm i)).comp
    (f := fun y : (ℝ × Aux (d + 2)) × Aux m =>
      (y.1.1, parameterFrame d (y.1.2 + coordinateInsertion σ y.2))) harg

/-- The pointwise cinematic condition constructs a joint inverse in all
center/base variables. The source can be chosen inside any neighborhood;
no uniform inverse or derivative bound is an additional hypothesis. -/
theorem Family.exists_movingLowerJet_analytic_chart {d : ℕ} (G : Family 2 d)
    {t : ℝ} {v : Aux (d + 2)}
    (ha : AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (t, parameterFrame d v))
    (hdet : G.cinematicDet (t, parameterFrame d v) ≠ 0) (m : ℕ) (hm : m ≤ d + 2)
    (U : Set ((ℝ × Aux (d + 2)) × Aux m)) (hU : U ∈ 𝓝 ((t, v), (0 : Aux m))) :
    ∃ (σ : Fin m ↪ Fin (d + 2))
      (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux m)
        ((ℝ × Aux (d + 2)) × Aux m)),
      ((t, v), (0 : Aux m)) ∈ e.source ∧ e.source ⊆ U ∧
      (∀ x, e x = (x.1, G.movingLowerJetMap hm σ x)) ∧
      AnalyticOnNhd ℝ e e.source ∧ AnalyticOnNhd ℝ e.symm e.target ∧
      (∀ y ∈ e.target, (e.symm y).1 = y.1 ∧ G.movingLowerJetMap hm σ (e.symm y) = y.2) ∧
      ∀ x ∈ e.source, AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
        (x.1.1, parameterFrame d (x.1.2 + coordinateInsertion σ x.2)) := by
  obtain ⟨σ, hσ⟩ := G.exists_cinematicInitialMinor hdet m hm
  let q : (ℝ × Aux (d + 2)) × Aux m := ((t, v), 0)
  have hF : AnalyticAt ℝ (G.movingLowerJetMap hm σ) q := by
    apply G.movingLowerJetMap_analyticAt
    simpa only [q, map_zero, add_zero] using ha
  have hi : (fderiv ℝ (fun z => G.movingLowerJetMap hm σ (q.1, z)) q.2).IsInvertible := by
    apply isInvertible_of_det_coordinates
    change (LinearMap.toMatrix' (fderiv ℝ (G.lowerCinematicJetMap hm σ t v) 0).toLinearMap).det ≠ 0
    rw [G.lowerCinematicJetMap_fderiv_matrix hm σ ha]
    exact hσ
  let S := {x : (ℝ × Aux (d + 2)) × Aux m |
    AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2)
      (x.1.1, parameterFrame d (x.1.2 + coordinateInsertion σ x.2))}
  have hopen : IsOpen {x : ℝ × Parameters 2 d |
      AnalyticAt ℝ (fun y : ℝ × Parameters 2 d => G.γ y.1 y.2) x} := isOpen_analyticAt ℝ _
  have hmap : Continuous (fun x : (ℝ × Aux (d + 2)) × Aux m =>
      (x.1.1, parameterFrame d (x.1.2 + coordinateInsertion σ x.2))) :=
    continuous_fst.fst.prodMk ((parameterFrame d).continuous.comp
      (continuous_fst.snd.add ((coordinateInsertion σ).continuous.comp continuous_snd)))
  have hS : IsOpen S := hopen.preimage hmap
  have hqS : q ∈ S := by simpa only [S, q, mem_setOf_eq, map_zero, add_zero] using ha
  obtain ⟨e, hq, hsub, he, hea, hei, hinv⟩ := exists_retainedParameter_analytic_chart hF hi
    (U ∩ S) (inter_mem hU (hS.mem_nhds hqS))
  exact ⟨σ, e, hq, fun x hx => (hsub hx).1, he, hea, hei, hinv,
    fun x hx => (hsub hx).2⟩

end PlanarNikodym
