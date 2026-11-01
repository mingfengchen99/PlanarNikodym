import PlanarNikodym.Reduction.FamilyReduction
import PlanarNikodym.Core.ReuseBasics
import Mathlib.Topology.Compactness.SigmaCompact

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- Fixed-curve centre fibres are sigma-compact in every finite auxiliary
dimension. The parameter domain is open and the time slices continuous.
This is a specific closed-fibre projection argument, not measurability of
arbitrary Borel projections. -/
theorem Family.centers_isSigmaCompact {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hγ : ∀ t ∈ G.I.carrier, ContinuousOn (G.γ t) G.W)
    (β : Set Plane) : IsSigmaCompact (G.centersOf β) := by
  classical
  by_cases hβ : ∃ q ∈ G.W, G.curve q = β
  · obtain ⟨q, hq, hqβ⟩ := hβ
    letI : LocallyCompactSpace G.W := hW.locallyCompactSpace
    let S : Set G.W := ⋂ t : G.I.carrier, {p | G.γ t p.val = G.γ t q}
    have hS : IsClosed S := by
      apply isClosed_iInter
      intro t
      exact isClosed_eq (continuousOn_iff_continuous_restrict.mp (hγ t t.property)) continuous_const
    have hσ : IsSigmaCompact S := isSigmaCompact_univ.of_isClosed_subset hS (subset_univ S)
    have himage : (fun p : G.W => p.val.1) '' S = G.centersOf β := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        apply (G.mem_centersOf β p.val.1).mpr
        refine ⟨p.val.2, p.property, ?_⟩
        have he : G.SameCurve p.val q := fun t ht => mem_iInter.mp hp ⟨t, ht⟩
        exact ((G.sameCurve_iff_curve_eq _ _).mp he).trans hqβ
      · intro hz
        obtain ⟨u, hu, hcurve⟩ := (G.mem_centersOf β z).mp hz
        refine ⟨⟨(z, u), hu⟩, mem_iInter.mpr ?_, rfl⟩
        intro t
        exact (G.sameCurve_iff_curve_eq (z, u) q).mpr (hcurve.trans hqβ.symm) t t.property
    rw [← himage]
    exact hσ.image (continuous_fst.comp continuous_subtype_val)
  · have he : G.centersOf β = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨u, hu, he⟩ := (G.mem_centersOf β z).mp hz
      exact hβ ⟨(z, u), hu, he⟩
    rw [he]
    exact isSigmaCompact_empty

theorem Family.centers_measurable_of_open_continuous {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hγ : ∀ t ∈ G.I.carrier, ContinuousOn (G.γ t) G.W)
    (β : Set Plane) : MeasurableSet (G.centersOf β) := by
  obtain ⟨K, hK, hcov⟩ := G.centers_isSigmaCompact hW hγ β
  rw [← hcov]
  exact MeasurableSet.iUnion (fun n => (hK n).measurableSet)

theorem Family.centers_measurable_of_analytic {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (β : Set Plane) :
    MeasurableSet (G.centersOf β) :=
  G.centers_measurable_of_open_continuous hW
    (fun t ht p hp => (G.parameter_analytic ha p hp ⟨t, ht⟩).continuousAt.continuousWithinAt) β

end PlanarNikodym
