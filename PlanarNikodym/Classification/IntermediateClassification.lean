import PlanarNikodym.Projection.ProjectionTransfer

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.localReuseNotCovered_mono_of_all {d e : ℕ} (H : Family 2 e) (G : Family 2 d)
    (ha : H.IsAnalytic) (hlocal : ∀ p ∈ G.W, G.LocallyReused p)
    (hcurves : ∀ z, H.curvesAtOn H.W z ⊆ G.curvesAtOn G.W z)
    (hH : H.LocalReuseNotCovered) : G.LocalReuseNotCovered := by
  intro V
  apply (hH V).mono
  rintro z ⟨u, hlu, hn⟩
  obtain ⟨v, hv, he⟩ := hcurves z ⟨u, hlu.1, rfl⟩
  refine ⟨v, hlocal (z, v) hv, ?_⟩
  intro hG
  exact hn (H.covered_of_curve_eq G ha.isSmooth (z, u) hlu.1 (z, v) V he.symm hG)

theorem full_intermediate_classification (hP : ProjectionConstructionInput)
    (hA : ProjectionAvoidanceInput) {d : ℕ} (hd : 0 < d) (G : Family 2 d)
    (hWne : G.W.Nonempty) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G d (d + 1)) :
    G.AdmitsNikodym ∧ G.HasLocalCurveReuse ∧ G.LocalReuseNotCovered := by
  obtain ⟨q, hq⟩ := hWne
  obtain ⟨M⟩ := exists_intermediate_model G hW ha (fun p hp => (hr p hp).1)
    (fun p hp => (hr p hp).2) q hq
  exact ⟨M.admitsNikodym hP hd ha,
    intermediate_hasLocalCurveReuse G ⟨q, hq⟩ hW ha hr,
    M.localReuseNotCovered hA hd hW ha hr⟩

/-- The positive intermediate-rank branch. All reductions and transfers are
proved. The remaining scalar construction and scalar jet/Fubini results are
the two explicit input arguments, whose full types are in ProjectionInputs. -/
theorem theorem_1_5_case_positive_intermediate (hP : ProjectionConstructionInput)
    (hA : ProjectionAvoidanceInput) {d m : ℕ} (hm : 0 < m) (G : Family 2 d)
    (hWne : G.W.Nonempty) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G m (m + 1)) :
    G.AdmitsNikodym ∧ G.HasLocalCurveReuse ∧ G.LocalReuseNotCovered := by
  obtain ⟨q, hq⟩ := hWne
  obtain ⟨U, _, _, hUW, Wz, Wu, H, hzO, huO, hqz, huNe, _, hprod, hHa, hHr, he⟩ :=
    corollary_6_2 G hW ha (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2) q hq
  have hHne : H.W.Nonempty := by
    obtain ⟨u, hu⟩ := huNe
    exact ⟨(q.1, u), hprod ▸ ⟨hqz, hu⟩⟩
  obtain ⟨hNik, _, hAvoid⟩ := full_intermediate_classification hP hA hm H hHne
    (hprod ▸ hzO.prod huO) hHa hHr
  have hcurves : ∀ z, H.curvesAtOn H.W z ⊆ G.curvesAtOn G.W z := by
    intro z β hβ
    obtain ⟨u, hu, hcurve⟩ := (he z).symm ▸ hβ
    exact ⟨u, hUW hu, hcurve⟩
  exact ⟨H.admitsNikodym_mono G hcurves hNik,
    intermediate_hasLocalCurveReuse G ⟨q, hq⟩ hW ha hr,
    H.localReuseNotCovered_mono_of_all G hHa (intermediate_locallyReused G hW ha hr)
      hcurves hAvoid⟩

end PlanarNikodym
