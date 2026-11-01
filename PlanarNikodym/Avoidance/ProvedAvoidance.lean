import PlanarNikodym.Avoidance.AvoidanceNullity
import PlanarNikodym.Avoidance.ProjectionCenters
import PlanarNikodym.Analysis.Maximal.SmoothAnalysisClassification

noncomputable section
namespace PlanarNikodym

/-- The full scalar avoidance input of §7.3 is proved from the actual
ProjectionModel. The output contains a positive-measure compact centre
subset, hence satisfies the original positive-inner-measure requirement. -/
theorem projection_avoidance_input : ProjectionAvoidanceInput := by
  intro d hd D V
  exact D.uncoveredTrace_hasPositivePart_of_timeCovered_null V
    (D.timeCovered_parameters_null hd V)

theorem full_intermediate_localReuseNotCovered_proved {d : ℕ} (hd : 0 < d)
    (G : Family 2 d) (hWne : G.W.Nonempty) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G d (d + 1)) : G.LocalReuseNotCovered := by
  obtain ⟨q, hq⟩ := hWne
  obtain ⟨M⟩ := exists_intermediate_model G hW ha (fun p hp => (hr p hp).1)
    (fun p hp => (hr p hp).2) q hq
  exact M.localReuseNotCovered projection_avoidance_input hd hW ha hr

/-- The local-reuse-not-covered conclusion of the positive intermediate
branch is now unconditional, independently of the remaining Nikodym-set
construction. Auxiliary variables are reduced by the proved normal form. -/
theorem positive_intermediate_localReuseNotCovered_proved {d m : ℕ} (hm : 0 < m)
    (G : Family 2 d) (hWne : G.W.Nonempty) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G m (m + 1)) : G.LocalReuseNotCovered := by
  obtain ⟨q, hq⟩ := hWne
  obtain ⟨U, _, _, hUW, Wz, Wu, H, hzO, huO, hqz, huNe, _, hprod, hHa, hHr, he⟩ :=
    corollary_6_2 G hW ha (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2) q hq
  have hHne : H.W.Nonempty := by
    obtain ⟨u, hu⟩ := huNe
    exact ⟨(q.1, u), hprod ▸ ⟨hqz, hu⟩⟩
  have hAvoid := full_intermediate_localReuseNotCovered_proved hm H hHne
    (hprod ▸ hzO.prod huO) hHa hHr
  have hcurves : ∀ z, H.curvesAtOn H.W z ⊆ G.curvesAtOn G.W z := by
    intro z β hβ
    obtain ⟨u, hu, hcurve⟩ := (he z).symm ▸ hβ
    exact ⟨u, hUW hu, hcurve⟩
  exact H.localReuseNotCovered_mono_of_all G hHa (intermediate_locallyReused G hW ha hr)
    hcurves hAvoid

/-- Compatibility with the original analytic route: callers no longer
need to supply a scalar avoidance proof. -/
theorem P8RemainingInputs.of_analysis_projection (hA : CinematicAnalysisInput)
    (hP : ProjectionConstructionInput) : P8RemainingInputs :=
  ⟨hA, hP, projection_avoidance_input⟩

/-- The constant-rank classification now retains only the high-frequency
analytic construction and the scalar null-set construction. -/
theorem theorem_1_5_after_avoidance (hA : CinematicSmoothAnalysisInput)
    (hP : ProjectionConstructionInput) : Theorem15Statement :=
  theorem_1_5_from_smooth_analysis hA hP projection_avoidance_input

theorem theorem_1_4_after_avoidance (hA : CinematicSmoothAnalysisInput)
    (hP : ProjectionConstructionInput) (H : ConnectedCellInput) : Theorem14Statement :=
  theorem_1_4_from_smooth_analysis hA hP projection_avoidance_input H

theorem proposition_1_6_after_avoidance (hA : CinematicSmoothAnalysisInput)
    (hP : ProjectionConstructionInput) (H : AnalyticCellInput) : Proposition16Statement :=
  proposition_1_6_from_smooth_analysis hA hP projection_avoidance_input H

end PlanarNikodym
