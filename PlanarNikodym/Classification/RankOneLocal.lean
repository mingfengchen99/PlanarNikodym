import PlanarNikodym.Classification.RankOneCoordinates
import PlanarNikodym.Geometry.IncidenceCenters
import PlanarNikodym.Geometry.OneParameterNull

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal
namespace PlanarNikodym

theorem zero_parameters_eq (p : Parameters 2 0) : p = (p.1, 0) :=
  Prod.ext rfl (Subsingleton.elim _ _)

namespace RankOneChart
variable {G : Family 2 0} (C : RankOneChart G)

def domain : Set (Parameters 2 0) := {p | C.K.symm p.1 ∈ C.F.target}
def lift (p : Parameters 2 0) : Plane := C.F.symm (C.K.symm p.1)

theorem domain_open : IsOpen C.domain :=
  C.F.open_target.preimage (C.K.symm.continuous.comp continuous_fst)

theorem domain_subset : C.domain ⊆ G.W := by
  intro p hp
  have h := C.target_subset _ hp
  rw [C.K.apply_symm_apply] at h
  rwa [← zero_parameters_eq p] at h

theorem lift_source (p : Parameters 2 0) (hp : p ∈ C.domain) : C.lift p ∈ C.F.source :=
  C.F.map_target hp

theorem lift_eq (p : Parameters 2 0) (hp : p ∈ C.domain) :
    (C.K (C.F (C.lift p)), 0) = p := by
  change (C.K (C.F (C.F.symm (C.K.symm p.1))), 0) = p
  rw [C.F.right_inv hp, C.K.apply_symm_apply, ← zero_parameters_eq p]

theorem base_source : C.base ∈ C.F.source := by
  rw [C.source_eq]
  exact ⟨mem_ball_self C.radius_pos, mem_ball_self C.radius_pos⟩

theorem domain_base {q : Parameters 2 0} (hq : C.K (C.F C.base) = q.1) : q ∈ C.domain := by
  change C.K.symm q.1 ∈ C.F.target
  rw [← hq, C.K.symm_apply_apply]
  exact C.F.map_source C.base_source

theorem completelyCovered (ha : G.IsAnalytic) : G.CompletelyCovered C.domain := by
  have hn : ∀ s ∈ ball C.base.2 C.radius, ∃ t ∈ G.I.carrier,
      deriv (fun r => C.h (t, r)) s ≠ 0 := by
    intro s hs
    obtain ⟨t, ht, hn⟩ := C.h_nontrivial s hs
    exact ⟨t, ht, by rwa [partialParameter_eq_deriv _ _ (C.h_analytic _ ⟨ht, hs⟩).differentiableAt] at hn⟩
  obtain ⟨V, hV⟩ := lemma_7_1_finite_exceptions G.I _ C.h C.h_analytic hn
  refine ⟨V, ?_⟩
  intro p hp
  let x := C.lift p
  have hx := C.lift_source p hp
  have hxs : x.2 ∈ ball C.base.2 C.radius := (C.source_eq ▸ hx).2
  obtain ⟨Z, hZ, hz⟩ := hV x.2 hxs
  have he : ∀ t ∈ G.I.carrier, G.γ t p = C.h (t, x.2) := by
    intro t ht
    rw [← C.lift_eq p hp]
    exact C.identity x hx t ht
  exact G.covered_of_equal_time_function ha.isSmooth p (C.domain_subset hp) V
    (fun t => C.h (t, x.2)) he Z hZ hz

theorem incidence_null (ha : G.IsAnalytic) (E : Set Plane)
    (hE : MeasurableSet E) (hE0 : volume E = 0) :
    volume (G.incidenceCenters C.domain E) = 0 := by
  let B := {s | s ∈ ball C.base.2 C.radius ∧
    0 < volume {t | t ∈ G.I.carrier ∧ (t, C.h (t, s)) ∈ E}}
  have hB : volume B = 0 := one_parameter_bad_parameters_null G.I _ isOpen_ball.measurableSet
    C.h C.h_analytic C.h_nontrivial E hE hE0
  let A := C.F.source ∩ ((univ : Set ℝ) ×ˢ B)
  have hA : volume A = 0 := by
    apply measure_mono_null inter_subset_right
    change (volume.prod volume) (univ ×ˢ B) = 0
    rw [Measure.prod_prod, hB, mul_zero]
  have him := analytic_image_null_coordinates C.K C.F C.F.source C.analytic A
    inter_subset_left hA
  apply measure_mono_null (t := (fun x => C.K (C.F x)) '' A) _ him
  rintro z ⟨u, hu, hp⟩
  let p : Parameters 2 0 := (z, u)
  let x := C.lift p
  have hx : x ∈ C.F.source := C.lift_source p hu
  have hxe : (C.K (C.F x), 0) = p := C.lift_eq p hu
  have htpos := (G.smooth_graph_positive_iff ha.isSmooth p (C.domain_subset hu) E).mp hp
  have he : G.hitTimes p E = {t | t ∈ G.I.carrier ∧ (t, C.h (t, x.2)) ∈ E} := by
    ext t
    by_cases ht : t ∈ G.I.carrier
    · have hv : G.γ t p = C.h (t, x.2) := by
        rw [← hxe]
        exact C.identity x hx t ht
      simp only [Family.hitTimes, Family.graphMap, mem_setOf_eq, hv]
    · simp [Family.hitTimes, ht]
  refine ⟨x, ⟨hx, mem_univ _, (C.source_eq ▸ hx).2, ?_⟩, congrArg Prod.fst hxe⟩
  rwa [← he]

theorem reused_base {q : Parameters 2 0} (hq : C.K (C.F C.base) = q.1) :
    HasPositivePart (Measure.hausdorffMeasure 1)
      ((G.restrictTo C.domain).centersOf (G.curve q)) := by
  let r := C.radius / 2
  have hr : 0 < r := half_pos C.radius_pos
  let T := Icc (C.base.1 - r) (C.base.1 + r)
  let ψ : ℝ → Base 2 := fun x => C.K (C.F (x, C.base.2))
  let P : Base 2 → ℝ := fun z => (C.K.symm z).1
  have hsource (t : ℝ) (ht : t ∈ T) : (t, C.base.2) ∈ C.F.source := by
    change C.base.1 - C.radius / 2 ≤ t ∧ t ≤ C.base.1 + C.radius / 2 at ht
    rw [C.source_eq]
    refine ⟨?_, mem_ball_self C.radius_pos⟩
    rw [mem_ball, Real.dist_eq]
    apply lt_of_le_of_lt (abs_le.mpr ⟨?_, ?_⟩) (half_lt_self C.radius_pos)
    · linarith [ht.1]
    · linarith [ht.2]
  have hcont : ContinuousOn ψ T := C.K.continuous.comp_continuousOn
    (C.F.continuousOn.comp (continuousOn_id.prodMk continuousOn_const) hsource)
  have hP : LipschitzWith _ P := LipschitzWith.prod_fst.comp C.K.symm.lipschitz
  have hleft : ∀ t ∈ T, P (ψ t) = t := by
    intro t ht
    change (C.K.symm (C.K (C.F (t, C.base.2)))).1 = t
    rw [C.K.symm_apply_apply, C.keep_first]
  have hpos := positive_part_of_curve_left_inverse ψ P hP (by linarith : C.base.1 - r < C.base.1 + r)
    hcont hleft
  apply hpos.mono
  rintro z ⟨t, ht, rfl⟩
  have hs := hsource t ht
  apply ((G.restrictTo C.domain).mem_centersOf _ _).mpr
  refine ⟨0, ?_, ?_⟩
  · change C.K.symm (C.K (C.F (t, C.base.2))) ∈ C.F.target
    rw [C.K.symm_apply_apply]
    exact C.F.map_source hs
  · apply Set.image_congr
    intro s hsI
    change (s, G.γ s (ψ t, 0)) = (s, G.γ s q)
    congr 1
    have hqparam : (C.K (C.F C.base), 0) = q :=
      Prod.ext hq (Subsingleton.elim _ _)
    rw [← hqparam, C.identity _ hs s hsI, C.identity _ C.base_source s hsI]

end RankOneChart

theorem rank_one_zero_aux_local (G : Family 2 0) (hW : IsOpen G.W) (ha : G.IsAnalytic)
    (hc : ∀ p ∈ G.W, G.curveRank p = 1) (q : Parameters 2 0) (hq : q ∈ G.W) :
    ∃ U : Set (Parameters 2 0), IsOpen U ∧ q ∈ U ∧ U ⊆ G.W ∧
      G.CompletelyCovered U ∧
      (∀ E, MeasurableSet E → volume E = 0 → volume (G.incidenceCenters U E) = 0) ∧
      HasPositivePart (Measure.hausdorffMeasure 1) ((G.restrictTo U).centersOf (G.curve q)) := by
  obtain ⟨C, hC⟩ := exists_rank_one_chart G hW ha hc q hq
  exact ⟨C.domain, C.domain_open, C.domain_base hC, C.domain_subset,
    C.completelyCovered ha, C.incidence_null ha, C.reused_base hC⟩

end PlanarNikodym
