import PlanarNikodym.Classification.ConstantRankClassification
import PlanarNikodym.Examples.ClassificationExamples

noncomputable section
open Set Module Submodule
namespace PlanarNikodym.Examples

/-- Here the centre records intercept and slope, with no selectable auxiliary
parameter. This exercises the maximal rank gap at the boundary d=0. -/
abbrev affineGraphs (I : Interval) : Family 2 0 :=
  ⟨I, univ, fun t p => p.1 0 + t * p.1 1⟩

theorem affineGraphs_analytic (I : Interval) : (affineGraphs I).IsAnalytic := by
  intro p _
  have hz : AnalyticAt ℝ (fun x : ℝ × Parameters 2 0 => x.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  exact (((ContinuousLinearMap.proj 0 : Base 2 →L[ℝ] ℝ).analyticAt _).comp hz).add
    (analyticAt_fst.mul (((ContinuousLinearMap.proj 1 : Base 2 →L[ℝ] ℝ).analyticAt _).comp hz))

theorem affineGraphs_zColumn (I : Interval) (p : Parameters 2 0) :
    (affineGraphs I).zColumn p = ![1, fun t : I.carrier => (t : ℝ)] := by
  funext i t
  change fderiv ℝ (fun z : Base 2 => z 0 + (t : ℝ) * z 1) p.1 (Pi.single i 1) = _
  have hf : HasFDerivAt (fun z : Base 2 => z 0 + (t : ℝ) * z 1)
      ((ContinuousLinearMap.proj (0 : Fin 2) : Base 2 →L[ℝ] ℝ) +
        (t : ℝ) • ContinuousLinearMap.proj (1 : Fin 2)) p.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p.1).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p.1).const_mul (t : ℝ))
  rw [hf.fderiv]
  fin_cases i <;> simp

theorem affineGraphs_ranks (I : Interval) (p : Parameters 2 0) :
    (affineGraphs I).pointRank p = 0 ∧ (affineGraphs I).curveRank p = 2 := by
  refine ⟨Family.pointRank_zero_aux _ _, ?_⟩
  have hzero : (affineGraphs I).pointSpace p = ⊥ := by
    simp [Family.pointSpace, Set.range_eq_empty]
  rw [Family.curveRank, Family.curveSpace, hzero, bot_sup_eq, affineGraphs_zColumn]
  exact (finrank_span_eq_card (independent_one_id I)).trans (Fintype.card_fin 2)

theorem affineGraphs_no_reuse (I : Interval) (β : Set Plane) :
    ((affineGraphs I).centersOf β).Countable ∧ ¬ (affineGraphs I).Reused β :=
  ⟨maximal_gap_centers_countable (affineGraphs I) isOpen_univ (affineGraphs_analytic I)
      (fun p _ => affineGraphs_ranks I p) β,
    maximal_gap_not_reused (affineGraphs I) isOpen_univ (affineGraphs_analytic I)
      (fun p _ => affineGraphs_ranks I p) β⟩

theorem affineGraphs_no_nikodym (hB : BocherInput) (hC : CinematicNullInput) (I : Interval) :
    ¬ (affineGraphs I).AdmitsNikodym :=
  (theorem_1_5_case_maximal_gap hB hC (affineGraphs I) isOpen_univ (affineGraphs_analytic I)
    (fun p _ => affineGraphs_ranks I p)).1

theorem lines_locallyReused (I : Interval) (p : Parameters 2 1) : (lines I).LocallyReused p :=
  intermediate_locallyReused (lines I) isOpen_univ (lines_analytic I)
    (fun p _ => lines_ranks I p) p (mem_univ p)

theorem horizontal_projection_model (I : Interval) : Nonempty (IntermediateModel (horizontal I)) :=
  exists_intermediate_model (horizontal I) isOpen_univ (horizontal_analytic I)
    (fun p _ => (horizontal_ranks I p).1) (fun p _ => (horizontal_ranks I p).2) 0 (mem_univ 0)

theorem lines_classification (hP : ProjectionConstructionInput) (hA : ProjectionAvoidanceInput)
    (I : Interval) :
    (lines I).AdmitsNikodym ∧ (lines I).HasLocalCurveReuse ∧ (lines I).LocalReuseNotCovered :=
  theorem_1_5_case_positive_intermediate hP hA (by norm_num : 0 < 1) (lines I)
    univ_nonempty isOpen_univ (lines_analytic I) (fun p _ => lines_ranks I p)

/-- The conditional assembly is instantiated on an actual bounded open
parameter domain. All ranks are inherited from the explicit line formula. -/
theorem bounded_lines_classification (inputs : P5Inputs) (I : Interval) :
    ConstantRankConclusions ((lines I).restrictTo (Metric.ball 0 1)) 1 2 := by
  apply theorem_1_5_conditional inputs 1 ((lines I).restrictTo (Metric.ball 0 1)) 1 2
    ⟨0, Metric.mem_ball_self (by norm_num)⟩ Metric.isOpen_ball Metric.isBounded_ball
    ((lines_analytic I).restrictTo (subset_univ _))
  exact fun p _ => lines_ranks I p

end PlanarNikodym.Examples
