import PlanarNikodym.Core.ReuseBasics

noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

/-- With no auxiliary variable, projection introduces no new existential
quantifier. A Borel parameter domain and ambient-continuous time slices give
Borel curve-centre fibres, including fibres of curves not in the family. -/
theorem zero_aux_centers_measurable (G : Family 2 0) (hW : MeasurableSet G.W)
    (hγ : ∀ t ∈ G.I.carrier, Continuous (G.γ t)) (β : Set Plane) :
    MeasurableSet (G.centersOf β) := by
  classical
  by_cases hne : (G.centersOf β).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    obtain ⟨u₀, _, hc₀⟩ := (G.mem_centersOf β z₀).mp hz₀
    let q : Parameters 2 0 := (z₀, u₀)
    let S := ⋂ t : G.I.carrier, {z : Base 2 | G.γ t (z, 0) = G.γ t q}
    have hS : IsClosed S := by
      apply isClosed_iInter
      intro t
      exact isClosed_eq ((hγ t t.property).comp (continuous_id.prodMk continuous_const)) continuous_const
    have he : G.centersOf β = (fun z : Base 2 => (z, (0 : Aux 0))) ⁻¹' G.W ∩ S := by
      ext z
      constructor
      · intro hz
        obtain ⟨u, hu, hc⟩ := (G.mem_centersOf β z).mp hz
        have hu0 : u = 0 := Subsingleton.elim _ _
        subst u
        refine ⟨hu, mem_iInter.mpr ?_⟩
        intro t
        exact (G.sameCurve_iff_curve_eq (z, 0) q).mpr (hc.trans hc₀.symm) t t.property
      · rintro ⟨hz, hs⟩
        apply (G.mem_centersOf β z).mpr
        refine ⟨0, hz, ?_⟩
        have hc : G.curve (z, 0) = G.curve q := (G.sameCurve_iff_curve_eq _ _).mp
          (fun t ht => mem_iInter.mp hs ⟨t, ht⟩)
        exact hc.trans hc₀
    rw [he]
    exact (hW.preimage (continuous_id.prodMk continuous_const).measurable).inter hS.measurableSet
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact MeasurableSet.empty

end PlanarNikodym
