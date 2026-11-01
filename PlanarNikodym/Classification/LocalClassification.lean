import PlanarNikodym.Classification.RankOneLocal

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem Family.covered_incidence_of_local {d : ℕ} (G : Family 2 d) (hWne : G.W.Nonempty)
    (hlocal : ∀ q ∈ G.W, ∃ U : Set (Parameters 2 d), IsOpen U ∧ q ∈ U ∧
      G.CompletelyCovered U ∧
      ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters U E) = 0) :
    G.CompletelyCovered G.W ∧
      ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  classical
  haveI : Nonempty G.W := hWne.to_subtype
  choose U hU using (fun q : G.W => hlocal q q.property)
  choose V hV using (fun q : G.W => (hU q).2.2.1)
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof G.W).indexed_countable_subcover U
    (fun q => (hU q).1) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, (hU ⟨p, hp⟩).2.1⟩)
  constructor
  · refine ⟨Family.Foliations.iUnion (fun n => V (f n)), ?_⟩
    intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hp)
    exact G.covered_iUnion _ n p (hV (f n) p hn)
  · intro E hE hE0
    apply measure_mono_null (t := ⋃ n : ℕ, G.incidenceCenters (U (f n)) E)
    · rintro z ⟨u, hu, hp⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hu)
      exact mem_iUnion.mpr ⟨n, u, hn, hp⟩
    · exact measure_iUnion_null (fun n => (hU (f n)).2.2.2 E hE hE0)

theorem rank_one_zero_aux_global (G : Family 2 0) (hWne : G.W.Nonempty)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hc : ∀ p ∈ G.W, G.curveRank p = 1) :
    G.CompletelyCovered G.W ∧
      ∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters G.W E) = 0 := by
  apply G.covered_incidence_of_local hWne
  intro q hq
  obtain ⟨U, ho, hqU, _, hcov, hnull, _⟩ := rank_one_zero_aux_local G hW ha hc q hq
  exact ⟨U, ho, hqU, hcov, hnull⟩

theorem rank_one_zero_aux_locallyReused (G : Family 2 0) (hW : IsOpen G.W)
    (ha : G.IsAnalytic) (hc : ∀ p ∈ G.W, G.curveRank p = 1)
    (q : Parameters 2 0) (hq : q ∈ G.W) : G.LocallyReused q := by
  refine ⟨hq, ?_⟩
  intro U hU
  obtain ⟨V, hV, hVo, hqV⟩ := mem_nhds_iff.mp (inter_mem hU (hW.mem_nhds hq))
  let H := G.restrictTo V
  have hVW : V ⊆ G.W := fun p hp => (hV hp).2
  obtain ⟨L, _, _, hLV, _, _, hpos⟩ := rank_one_zero_aux_local H hVo (ha.restrictTo hVW)
    (fun p hp => hc p (hVW hp)) q hqV
  apply hpos.mono
  intro z hz
  obtain ⟨u, hu, he⟩ := ((H.restrictTo L).mem_centersOf _ z).mp hz
  exact ⟨(z, u), ⟨⟨hVW (hLV hu), he⟩, (hV (hLV hu)).1⟩, rfl⟩

end PlanarNikodym
