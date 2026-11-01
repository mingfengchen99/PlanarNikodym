import PlanarNikodym.Geometry.FiniteRigidity
import PlanarNikodym.Core.ReuseBasics
import PlanarNikodym.Core.Statements

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.centers_countable_of_local {d : ℕ} (G : Family 2 d)
    (h : ∀ q ∈ G.W, ∃ U : Set (Parameters 2 d), IsOpen U ∧ q ∈ U ∧
      ∀ β : Set Plane, ((G.restrictTo U).centersOf β).Countable)
    (β : Set Plane) : (G.centersOf β).Countable := by
  classical
  choose U hU using h
  obtain ⟨T, hTc, hT⟩ := (HereditarilyLindelofSpace.isLindelof G.W).elim_countable_subcover
    (fun q : G.W => U q q.property) (fun q => (hU q q.property).1) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, (hU p hp).2.1⟩)
  haveI := hTc.to_subtype
  apply (countable_iUnion (fun q : T => (hU q.val q.val.property).2.2 β)).mono
  intro z hz
  obtain ⟨u, hu, he⟩ := (G.mem_centersOf β z).mp hz
  obtain ⟨q, hq, hmem⟩ := mem_iUnion₂.mp (hT hu)
  exact mem_iUnion.mpr ⟨⟨q, hq⟩,
    ((G.restrictTo (U q q.property)).mem_centersOf β z).mpr ⟨u, hmem, he⟩⟩

/-- The maximal rank gap forces countable reuse centres even in the presence
of redundant auxiliary variables. No analytic or measure-theoretic input is
left as a hypothesis beyond the assumptions of Theorem 1.5. -/
theorem maximal_gap_centers_countable {d m : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hr : ConstantRanks G m (m + 2))
    (β : Set Plane) : (G.centersOf β).Countable := by
  apply G.centers_countable_of_local _ β
  intro q hq
  obtain ⟨U, hUo, hqU, _, Wz, Wu, H, hzO, huO, _, _, _, hprod, hHa, hHr, he⟩ :=
    corollary_6_2 G hW ha (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2) q hq
  refine ⟨U, hUo, hqU, ?_⟩
  intro β
  have hsub : (G.restrictTo U).centersOf β ⊆ H.centersOf β := by
    intro z hz
    have hz' : β ∈ G.curvesAtOn U z := ((G.restrictTo U).mem_centersOf β z).mp hz
    have hzH : β ∈ H.curvesAtOn H.W z := (he z) ▸ hz'
    exact (H.mem_centersOf β z).mpr hzH
  exact (full_curve_rank_centers_countable H hHa (fun p hp => (hHr p hp).2) β).mono hsub

theorem maximal_gap_not_reused {d m : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hr : ConstantRanks G m (m + 2))
    (β : Set Plane) : ¬ G.Reused β := by
  haveI := Measure.noAtoms_hausdorff (Base 2) (by norm_num : (0 : ℝ) < 1)
  rintro ⟨A, hA, _, hp⟩
  exact hp.ne' (measure_mono_null hA
    ((maximal_gap_centers_countable G hW ha hr β).measure_zero (Measure.hausdorffMeasure 1)))

end PlanarNikodym
