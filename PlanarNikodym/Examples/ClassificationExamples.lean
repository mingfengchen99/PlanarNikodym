import PlanarNikodym.Classification.MassiveReuse
import PlanarNikodym.Classification.RankOneClassification
import PlanarNikodym.Examples.ReductionExamples

noncomputable section
open Set
namespace PlanarNikodym.Examples

theorem horizontal_analytic (I : Interval) : (horizontal I).IsAnalytic := by
  intro p hp
  have hz : AnalyticAt ℝ (fun x : ℝ × Parameters 2 0 => x.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  exact ((ContinuousLinearMap.proj 1 : Base 2 →L[ℝ] ℝ).analyticAt _).comp hz

theorem sliding_analytic (I : Interval) : (slidingHorizontal I).IsAnalytic := by
  intro p hp
  have hz : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hu : AnalyticAt ℝ (fun x : ℝ × Parameters 2 1 => x.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  exact (((ContinuousLinearMap.proj 1 : Base 2 →L[ℝ] ℝ).analyticAt _).comp hz).sub
    (((ContinuousLinearMap.proj 0 : Aux 1 →L[ℝ] ℝ).analyticAt _).comp hu)

theorem sliding_classification (I : Interval) :
    (slidingHorizontal I).AdmitsNikodym ∧ (slidingHorizontal I).HasMassiveCurveReuse :=
  theorem_1_5_case_equal (slidingHorizontal I) Set.univ_nonempty isOpen_univ
    (sliding_analytic I) (fun p _ => sliding_ranks I p)

theorem zero_rank_classification (I : Interval) :
    (constantFamily I).AdmitsNikodym ∧ (constantFamily I).HasMassiveCurveReuse :=
  theorem_1_5_case_equal (constantFamily I) Set.univ_nonempty isOpen_univ
    (fun _ _ => analyticAt_const) (fun p _ => constantFamily_ranks I p)

theorem horizontal_classification (I : Interval) :
    ¬ (horizontal I).AdmitsNikodym ∧ ¬ (horizontal I).HasMassiveCurveReuse ∧
      (∀ p, (horizontal I).LocallyReused p) ∧ (horizontal I).HasLocalCurveReuse ∧
      (horizontal I).ReusedStronglyCovered := by
  obtain ⟨hn, hm, hl, hh, hc⟩ := theorem_1_5_case_rank_one (horizontal I)
    Set.univ_nonempty isOpen_univ (horizontal_analytic I) (fun p _ => horizontal_ranks I p)
  exact ⟨hn, hm, fun p => hl p (mem_univ p), hh, hc⟩

/-- The rank-one branch with two unused auxiliary parameters exercises
the reduction to d=0, rather than assuming d=0 in the classification. -/
abbrev horizontalWithAux (I : Interval) : Family 2 2 := ⟨I, univ, fun _ p => p.1 1⟩

theorem horizontalWithAux_ranks (I : Interval) (p : Parameters 2 2) :
    (horizontalWithAux I).pointRank p = 0 ∧ (horizontalWithAux I).curveRank p = 1 := by
  have hu : (horizontalWithAux I).uColumn p = 0 := by
    funext i t
    change fderiv ℝ (fun _ : Aux 2 => p.1 1) p.2 (Pi.single i 1) = 0
    simp
  have hs : (horizontalWithAux I).pointSpace p = ⊥ := by
    change Submodule.span ℝ (range ((horizontalWithAux I).uColumn p)) = ⊥
    rw [hu]
    simp
  have hz : (horizontalWithAux I).zColumn p = (horizontal I).zColumn (p.1, 0) := rfl
  constructor
  · change Module.finrank ℝ ((horizontalWithAux I).pointSpace p) = 0
    rw [hs]
    simp
  · change Module.finrank ℝ ((horizontalWithAux I).pointSpace p ⊔
      Submodule.span ℝ (range ((horizontalWithAux I).zColumn p)) : Submodule ℝ (I.carrier → ℝ)) = 1
    rw [hs, hz, bot_sup_eq]
    have hold := (horizontal_ranks I (p.1, 0)).2
    have holdspace : (horizontal I).pointSpace (p.1, 0) = ⊥ := by
      simp [Family.pointSpace, Set.range_eq_empty]
    change Module.finrank ℝ ((horizontal I).pointSpace (p.1, 0) ⊔
      Submodule.span ℝ (range ((horizontal I).zColumn (p.1, 0))) : Submodule ℝ (I.carrier → ℝ)) = 1 at hold
    rwa [holdspace, bot_sup_eq] at hold

theorem horizontalWithAux_classification (I : Interval) :
    ¬ (horizontalWithAux I).AdmitsNikodym ∧ (horizontalWithAux I).HasLocalCurveReuse ∧
      (horizontalWithAux I).ReusedStronglyCovered := by
  have ha : (horizontalWithAux I).IsAnalytic := by
    intro p hp
    have hz : AnalyticAt ℝ (fun x : ℝ × Parameters 2 2 => x.2.1) p :=
      analyticAt_fst.comp analyticAt_snd
    exact ((ContinuousLinearMap.proj 1 : Base 2 →L[ℝ] ℝ).analyticAt _).comp hz
  obtain ⟨hn, _, _, hh, hc⟩ := theorem_1_5_case_rank_one (horizontalWithAux I)
    Set.univ_nonempty isOpen_univ ha (fun p _ => horizontalWithAux_ranks I p)
  exact ⟨hn, hh, hc⟩

end PlanarNikodym.Examples
