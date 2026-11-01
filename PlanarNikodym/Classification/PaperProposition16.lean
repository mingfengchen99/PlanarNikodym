import PlanarNikodym.Classification.GeneralAnalyticClassification

/-! D-R6: the four conclusions of the original Proposition 1.6, without
an additional finite disjoint parameter-cover requirement. The existing
stronger Proposition16Statement is preserved. The general classification
is proved first; a finite positive witness is then selected. -/
noncomputable section
open Set
namespace PlanarNikodym

def FiniteRankWitnessConclusions {d N : ℕ} (G : Family 2 d) (P : Fin N → RankPiece G) : Prop :=
  (G.AdmitsNikodym ↔ ∃ i, (P i).family.AdmitsNikodym) ∧
  (∀ i, ConstantRanks (P i).family (P i).point_rank (P i).curve_rank) ∧
  (G.HasMassiveCurveReuse ↔ ∃ i, (P i).family.HasMassiveCurveReuse) ∧
  (¬ G.HasMassiveCurveReuse →
    (G.LocalReuseNotCovered ↔ ∃ i, (P i).family.LocalReuseNotCovered))

theorem Family.exists_finite_rank_witnesses {d : ℕ} (G : Family 2 d)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    ∃ N : ℕ, N ≤ 1 ∧ ∃ P : Fin N → RankPiece G, FiniteRankWitnessConclusions G P := by
  classical
  by_cases hm : G.HasMassiveCurveReuse
  · obtain ⟨D⟩ := G.exists_analyticRankCover ho ha
    obtain ⟨P, _, hPm⟩ := D.hasMassiveCurveReuse_iff.mp hm
    have hGn := G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
    have hPn := P.family.admitsNikodym_of_hasMassiveCurveReuse P.analytic_family.isSmooth hPm
    refine ⟨1, le_rfl, fun _ => P, ?_⟩
    refine ⟨⟨fun _ => ⟨0, hPn⟩, fun _ => hGn⟩, (fun _ => P.ranks),
      ⟨fun _ => ⟨0, hPm⟩, fun _ => hm⟩, ?_⟩
    exact fun hn => (hn hm).elim
  · by_cases hn : G.AdmitsNikodym
    · obtain ⟨P, hPn⟩ := G.exists_rankPiece_of_admitsNikodym ho ha hn
      have hPm : ¬ P.family.HasMassiveCurveReuse :=
        fun h => hm (P.family.hasMassiveCurveReuse_mono G P.toAnalyticPiece.curves_mono h)
      have hPu : P.family.LocalReuseNotCovered :=
        ((constant_rank_classification p5_inputs_proved P.family P.connected_domain.nonempty
          P.open_domain P.analytic_family P.ranks).mp hPn).resolve_left hPm
      have hGu : G.LocalReuseNotCovered :=
        ((G.general_classification_proved ho ha).mp hn).resolve_left hm
      refine ⟨1, le_rfl, fun _ => P, ?_⟩
      refine ⟨⟨fun _ => ⟨0, hPn⟩, fun _ => hn⟩, (fun _ => P.ranks),
        ⟨fun h => (hm h).elim, ?_⟩, fun _ => ⟨fun _ => ⟨0, hPu⟩, fun _ => hGu⟩⟩
      rintro ⟨_, h⟩
      exact (hPm h).elim
    · have hGu : ¬ G.LocalReuseNotCovered :=
        fun h => hn ((G.general_classification_proved ho ha).mpr (Or.inr h))
      refine ⟨0, by omega, Fin.elim0, ?_⟩
      simp [FiniteRankWitnessConclusions, hn, hm, hGu]

/-- The paper's literal finite-family conclusion. Domain cover and
disjointness are not added to the four required equivalences. -/
def Proposition16PaperStatement : Prop :=
  ∀ (d : ℕ) (G : Family 2 d), AnalyticParameterDomain G → G.IsAnalyticAtClosure →
    ∃ (N : ℕ) (k : Fin N → ℕ) (H : (i : Fin N) → Family 2 (k i)),
      (∀ i, k i ≤ d ∧ (H i).I = G.I ∧ IsOpen (H i).W ∧
        Bornology.IsBounded (H i).W ∧ IsConnected (H i).W ∧ (H i).IsAnalytic) ∧
      (G.AdmitsNikodym ↔ ∃ i, (H i).AdmitsNikodym) ∧
      (∀ i, ∃ mp mc : ℕ, ConstantRanks (H i) mp mc) ∧
      (G.HasMassiveCurveReuse ↔ ∃ i, (H i).HasMassiveCurveReuse) ∧
      (¬ G.HasMassiveCurveReuse →
        (G.LocalReuseNotCovered ↔ ∃ i, (H i).LocalReuseNotCovered))

theorem proposition_1_6_paper_proved : Proposition16PaperStatement := by
  intro d G hdom ha
  obtain ⟨N, _, P, hNik, hr, hMass, hLocal⟩ := G.exists_finite_rank_witnesses hdom.1 ha.isAnalytic
  refine ⟨N, fun i => (P i).dim, fun i => (P i).family, ?_, hNik, ?_, hMass, hLocal⟩
  · intro i
    exact ⟨(P i).dim_le, (P i).interval_eq, (P i).open_domain, (P i).bounded_domain,
      (P i).connected_domain, (P i).analytic_family⟩
  · intro i
    exact ⟨(P i).point_rank, (P i).curve_rank, hr i⟩

end PlanarNikodym
