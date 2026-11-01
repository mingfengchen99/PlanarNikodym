import PlanarNikodym.Classification.ConstantRankClassification
import PlanarNikodym.Classification.ReuseLocalization

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem constant_ranks_trichotomy {d mp mc : ℕ} (G : Family 2 d)
    (hWne : G.W.Nonempty) (hr : ConstantRanks G mp mc) :
    mc = mp ∨ mc = mp + 1 ∨ mc = mp + 2 := by
  obtain ⟨q, hq⟩ := hWne
  simpa only [(hr q hq).1, (hr q hq).2] using G.rank_trichotomy q

/-- The negative constant-rank cases give outer-null incidence centres,
which is stronger than merely the negation of a Borel Nikodym witness. -/
theorem constant_rank_incidence_null_of_noNikodym (inputs : P5Inputs)
    {d mp mc : ℕ} (G : Family 2 d) (hWne : G.W.Nonempty) (hW : IsOpen G.W)
    (ha : G.IsAnalytic) (hr : ConstantRanks G mp mc) (hn : ¬ G.AdmitsNikodym) :
    ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  rcases constant_ranks_trichotomy G hWne hr with he | he | he
  · subst mc
    exact (hn (theorem_1_5_case_equal G hWne hW ha hr).1).elim
  · subst mc
    by_cases hz : mp = 0
    · subst mp
      exact (rank_one_global G hWne hW ha hr).2
    · exact (hn (theorem_1_5_case_positive_intermediate inputs.projectionConstruction
        inputs.projectionAvoidance (Nat.pos_of_ne_zero hz) G hWne hW ha hr).1).elim
  · subst mc
    exact maximal_gap_incidence_null inputs.bocher inputs.cinematicNull G hW ha hr

/-- This consequence is used in Proposition 1.6(4); it depends only on
Theorem 1.5 and never on a decomposition theorem. -/
theorem constant_rank_strong_cover_of_negative (inputs : P5Inputs)
    {d mp mc : ℕ} (G : Family 2 d) (hWne : G.W.Nonempty) (hW : IsOpen G.W)
    (ha : G.IsAnalytic) (hr : ConstantRanks G mp mc)
    (hm : ¬ G.HasMassiveCurveReuse) (hu : ¬ G.LocalReuseNotCovered) :
    G.ReusedStronglyCovered := by
  rcases constant_ranks_trichotomy G hWne hr with he | he | he
  · subst mc
    exact (hm (theorem_1_5_case_equal G hWne hW ha hr).2).elim
  · subst mc
    by_cases hz : mp = 0
    · subst mp
      exact (theorem_1_5_case_rank_one G hWne hW ha hr).2.2.2.2
    · exact (hu (theorem_1_5_case_positive_intermediate inputs.projectionConstruction
        inputs.projectionAvoidance (Nat.pos_of_ne_zero hz) G hWne hW ha hr).2.2).elim
  · subst mc
    exact ⟨Family.Foliations.zero, fun p _ hp => (maximal_gap_not_reused G hW ha hr _ hp).elim⟩

theorem constant_rank_noNikodym_of_negative (inputs : P5Inputs)
    {d mp mc : ℕ} (G : Family 2 d) (hWne : G.W.Nonempty) (hW : IsOpen G.W)
    (ha : G.IsAnalytic) (hr : ConstantRanks G mp mc)
    (hm : ¬ G.HasMassiveCurveReuse) (hu : ¬ G.LocalReuseNotCovered) : ¬ G.AdmitsNikodym := by
  rcases constant_ranks_trichotomy G hWne hr with he | he | he
  · subst mc
    exact (hm (theorem_1_5_case_equal G hWne hW ha hr).2).elim
  · subst mc
    by_cases hz : mp = 0
    · subst mp
      exact (theorem_1_5_case_rank_one G hWne hW ha hr).1
    · exact (hu (theorem_1_5_case_positive_intermediate inputs.projectionConstruction
        inputs.projectionAvoidance (Nat.pos_of_ne_zero hz) G hWne hW ha hr).2.2).elim
  · subst mc
    exact (theorem_1_5_case_maximal_gap inputs.bocher inputs.cinematicNull G hW ha hr).1

theorem constant_rank_classification (inputs : P5Inputs)
    {d mp mc : ℕ} (G : Family 2 d) (hWne : G.W.Nonempty) (hW : IsOpen G.W)
    (ha : G.IsAnalytic) (hr : ConstantRanks G mp mc) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  constructor
  · intro hn
    by_cases hm : G.HasMassiveCurveReuse
    · exact Or.inl hm
    · exact Or.inr (by
        by_contra hu
        exact constant_rank_noNikodym_of_negative inputs G hWne hW ha hr hm hu hn)
  · rintro (hm | hu)
    · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
    · by_contra hn
      have hm : ¬ G.HasMassiveCurveReuse :=
        fun hm => hn (G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm)
      rcases constant_ranks_trichotomy G hWne hr with he | he | he
      · subst mc
        exact hm (theorem_1_5_case_equal G hWne hW ha hr).2
      · subst mc
        by_cases hz : mp = 0
        · subst mp
          exact G.not_localReuseNotCovered_of_strong
            (theorem_1_5_case_rank_one G hWne hW ha hr).2.2.2.2 hu
        · exact hn (theorem_1_5_case_positive_intermediate inputs.projectionConstruction
            inputs.projectionAvoidance (Nat.pos_of_ne_zero hz) G hWne hW ha hr).1
      · subst mc
        exact G.not_localReuseNotCovered_of_strong
          ⟨Family.Foliations.zero, fun p _ hp => (maximal_gap_not_reused G hW ha hr _ hp).elim⟩ hu

end PlanarNikodym
