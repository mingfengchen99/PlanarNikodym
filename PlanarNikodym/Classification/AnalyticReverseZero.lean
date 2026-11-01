import PlanarNikodym.Classification.AnalyticCountableConsequences

/-! The full analytic classification when there are no auxiliary
parameters. Singular parameters then have null centres directly. Local
reuse is restricted to the open regular locus, so no closure assertion
for a countable exceptional set is used. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace PlanarNikodym

/-- The actual negative constant-rank classification gives a strong
cover of every reused curve; no decomposition input is involved. -/
theorem Family.analytic_strong_cover_of_noNikodym
    {d mp mc : ℕ} (G : Family 2 d) (hne : G.W.Nonempty)
    (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (hr : ConstantRanks G mp mc) (hn : ¬ G.AdmitsNikodym) :
    G.ReusedStronglyCovered := by
  apply constant_rank_strong_cover_of_negative p5_inputs_proved G hne ho ha hr
  · exact fun hm => hn (G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm)
  · exact fun hu => hn ((constant_rank_classification p5_inputs_proved G hne ho ha hr).mpr
      (Or.inr hu))

/-- On a connected open parameter domain with no auxiliary coordinates,
the actual singular rank locus projects into a null centre set. -/
theorem Family.zero_auxiliary_null_cover_connected (G : Family 2 0)
    (ho : IsOpen G.W) (hc : IsConnected G.W) (ha : G.IsAnalytic)
    (hn : ¬ G.AdmitsNikodym) : G.LocallyReusedCovered := by
  classical
  obtain ⟨M, _, _, hMo, hMd, hMr⟩ := generic_double_rank_minor G ho hc ha
  have hFa := M.productValue_analytic ho ha
  have hFn := M.productValue_nontrivial hc hMd
  obtain ⟨E, hEn, hflat⟩ :=
    exists_null_flat_auxiliary_fiber_exception ho hc.isPreconnected hFa hFn
  have hbad (p : Parameters 2 0) (hp : p ∈ G.W)
      (hpr : p ∉ M.regularSet) : p.1 ∈ E := by
    have hz : M.productValue p = 0 := by
      by_contra hz
      exact hpr ((M.mem_regularSet_iff_product p).mpr ⟨hp, hz⟩)
    apply hflat p hp
    exact Filter.Eventually.of_forall fun u => by
      have hu : u = p.2 := Subsingleton.elim _ _
      simpa only [hu] using hz
  let H := G.restrictTo M.regularSet
  have hsub : M.regularSet ⊆ G.W := fun _ hp => hp.1
  have hHa : H.IsAnalytic := fun x hx => ha x ⟨hx.1, hsub hx.2⟩
  have hHne : H.W.Nonempty := by
    obtain ⟨p, hp, hz⟩ := hFn
    exact ⟨p, (M.mem_regularSet_iff_product p).mpr ⟨hp, hz⟩⟩
  have hHn : ¬ H.AdmitsNikodym :=
    fun hi => hn (H.admitsNikodym_mono G
      (by intro z β hβ; obtain ⟨u, hu, he⟩ := hβ; exact ⟨u, hsub hu, he⟩) hi)
  obtain ⟨V, hV⟩ := H.analytic_strong_cover_of_noNikodym hHne hMo hHa hMr hHn
  refine ⟨V, measure_mono_null ?_ hEn⟩
  rintro z ⟨u, hl, hnc⟩
  by_contra hz
  have hr : (z, u) ∈ M.regularSet := by
    by_contra hr
    exact hz (hbad (z, u) hl.1 hr)
  have hlH := G.locallyReused_restrict_of_nhds M.regularSet (z, u)
    (hMo.mem_nhds hr) hl
  exact hnc (hV (z, u) hr hlH.reused)

/-- The actual null-cover certificate for an arbitrary open analytic
family with auxiliary dimension zero, including empty and unbounded
domains and domains with infinitely many connected components. -/
theorem Family.zero_auxiliary_null_cover (G : Family 2 0)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) (hn : ¬ G.AdmitsNikodym) :
    G.LocallyReusedCovered := by
  classical
  by_cases hne : G.W.Nonempty
  · obtain ⟨C⟩ := exists_ball_parameter_cover G ho hne
    let O := C.toOpenParameterCover
    apply O.locallyReusedCovered
    intro i
    apply (O.family i).zero_auxiliary_null_cover_connected (O.isOpen i)
      ((convex_ball (C.center i) (C.radius i)).isConnected
        ⟨C.center i, mem_ball_self (C.radius_pos i)⟩)
      (C.analyticAtClosure ha i).isAnalytic
    exact fun hi => hn ((O.family i).admitsNikodym_mono G (O.curves_mono i) hi)
  · refine ⟨Family.Foliations.zero, measure_mono_null ?_ measure_empty⟩
    rintro z ⟨u, hl, _⟩
    exact (hne ⟨(z, u), hl.1⟩).elim

/-- Both directions of Theorem 1.4 for zero auxiliary dimension. This is
not the higher-dimensional reverse classification. -/
theorem Family.zero_auxiliary_classification_proved (G : Family 2 0)
    (ho : IsOpen G.W) (ha : G.IsAnalytic) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered := by
  constructor
  · exact G.general_classification_forward_proved ho ha
  · rintro (hm | hu)
    · exact G.admitsNikodym_of_hasMassiveCurveReuse ha.isSmooth hm
    · by_contra hn
      exact G.not_localReuseNotCovered_of_null_cover (G.zero_auxiliary_null_cover ho ha hn) hu

/-- The original geometric assumptions specialized to dimension zero. -/
theorem theorem_1_4_zero_auxiliary_proved (G : Family 2 0)
    (ho : IsOpen G.W) (ha : G.IsAnalyticAtClosure) :
    G.AdmitsNikodym ↔ G.HasMassiveCurveReuse ∨ G.LocalReuseNotCovered :=
  G.zero_auxiliary_classification_proved ho ha.isAnalytic

end PlanarNikodym
