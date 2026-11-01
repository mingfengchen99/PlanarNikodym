import PlanarNikodym.Classification.LocalClassification
import PlanarNikodym.Core.Statements

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem rank_one_global {d : ℕ} (G : Family 2 d) (hWne : G.W.Nonempty)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hr : ConstantRanks G 0 1) :
    G.CompletelyCovered G.W ∧
      ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  apply G.covered_incidence_of_local hWne
  intro q hq
  obtain ⟨U, hUo, hqU, hUW, Wz, Wu, H, hzO, huO, hqz, huNe, _, hprod, hHa, hHr, he⟩ :=
    corollary_6_2 G hW ha (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2) q hq
  have hHne : H.W.Nonempty := by
    obtain ⟨u, hu⟩ := huNe
    exact ⟨(q.1, u), hprod ▸ ⟨hqz, hu⟩⟩
  obtain ⟨⟨V, hV⟩, hnull⟩ := rank_one_zero_aux_global H hHne (hprod ▸ hzO.prod huO) hHa
    (fun p hp => (hHr p hp).2)
  refine ⟨U, hUo, hqU, ⟨V, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨u, hu, hcurve⟩ := (he p.1) ▸ (show G.curve p ∈ G.curvesAtOn U p.1 from
      ⟨p.2, hp, rfl⟩)
    exact G.covered_of_curve_eq H ha.isSmooth p (hUW hp) (p.1, u) V hcurve.symm (hV _ hu)
  · intro E hE hE0
    exact measure_mono_null (G.incidenceCenters_mono H U H.W (fun z => (he z).subset) E)
      (hnull E hE hE0)

theorem rank_one_locallyReused {d : ℕ} (G : Family 2 d) (hW : IsOpen G.W)
    (ha : G.IsAnalytic) (hr : ConstantRanks G 0 1)
    (q : Parameters 2 d) (hq : q ∈ G.W) : G.LocallyReused q := by
  refine ⟨hq, ?_⟩
  intro U hU
  obtain ⟨V, hV, hVo, hqV⟩ := mem_nhds_iff.mp (inter_mem hU (hW.mem_nhds hq))
  let G₀ := G.restrictTo V
  have hVW : V ⊆ G.W := fun p hp => (hV hp).2
  obtain ⟨L, _, hqL, hLV, Wz, Wu, H, hzO, huO, _, _, _, hprod, hHa, hHr, he⟩ :=
    corollary_6_2 G₀ hVo (ha.restrictTo hVW) (fun p hp => (hr p (hVW hp)).1)
      (fun p hp => (hr p (hVW hp)).2) q hqV
  obtain ⟨u, hu, hcurve⟩ := (he q.1) ▸ (show G₀.curve q ∈ G₀.curvesAtOn L q.1 from
    ⟨q.2, hqL, rfl⟩)
  have hre := rank_one_zero_aux_locallyReused H (hprod ▸ hzO.prod huO) hHa
    (fun p hp => (hHr p hp).2) (q.1, u) hu
  have hpos : HasPositivePart (Measure.hausdorffMeasure 1) (H.centersOf (H.curve (q.1, u))) := by
    have hh := hre.2 univ (by simp)
    simpa only [Family.centersOf, inter_univ] using hh
  apply hpos.mono
  intro z hz
  have hz' : H.curve (q.1, u) ∈ H.curvesAtOn H.W z := (H.mem_centersOf _ z).mp hz
  obtain ⟨v, hv, hvc⟩ := (he z).symm ▸ hz'
  exact ⟨(z, v), ⟨⟨hVW (hLV hv), hvc.trans hcurve⟩, (hV (hLV hv)).1⟩, rfl⟩

/-- The rank-(0,1) branch of Theorem 1.5, including all reuse and foliation
clauses. All measure and geometric inputs are proved in this project or Mathlib. -/
theorem theorem_1_5_case_rank_one {d : ℕ} (G : Family 2 d) (hWne : G.W.Nonempty)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hr : ConstantRanks G 0 1) :
    ¬ G.AdmitsNikodym ∧ ¬ G.HasMassiveCurveReuse ∧
      (∀ p ∈ G.W, G.LocallyReused p) ∧ G.HasLocalCurveReuse ∧ G.ReusedStronglyCovered := by
  obtain ⟨⟨V, hV⟩, hnull⟩ := rank_one_global G hWne hW ha hr
  have hlocal := rank_one_locallyReused G hW ha hr
  exact ⟨G.no_nikodym_of_incidence_null hnull, G.no_massive_of_incidence_null ha.isSmooth hnull,
    hlocal, G.hasLocalCurveReuse_of_all hW hWne hlocal, ⟨V, fun p hp _ => hV p hp⟩⟩

end PlanarNikodym
