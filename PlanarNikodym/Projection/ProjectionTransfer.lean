import PlanarNikodym.Projection.ProjectionInputs

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

def centerCoordinates (j : Fin 2) : Plane ≃L[ℝ] Base 2 :=
  (planarCenterEquiv j).trans (ContinuousLinearEquiv.prodUnique ℝ (Base 2) (Aux 0))

theorem centerCoordinates_apply (j : Fin 2) (p : Plane) (i : Fin 2) :
    centerCoordinates j p i = if i = j then p.2 else p.1 := rfl

theorem positivePart_image_coordinates (K : Plane ≃L[ℝ] Base 2) (S : Set Plane)
    (hS : HasPositivePart volume S) : HasPositivePart volume (K '' S) := by
  obtain ⟨A, hAS, hA, hpos⟩ := hS
  refine ⟨K '' A, image_mono hAS, K.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hA, ?_⟩
  apply pos_iff_ne_zero.mpr
  intro hn
  have hback := linearEquiv_image_null K.symm volume volume (K '' A) hn
  have he : K.symm '' (K '' A) = A := by
    rw [image_image]
    simp only [K.symm_apply_apply, image_id']
  exact hpos.ne' (he ▸ hback)

/-- Hausdorff-a.e. graph coverage implies Lebesgue-a.e. time coverage.
This implication does not require measurability of the coverage predicate. -/
theorem Family.covered_by_times {d : ℕ} (G : Family 2 d) (ha : G.IsSmooth)
    (p : Parameters 2 d) (hp : p ∈ G.W) (V : Family.Foliations) (hV : G.Covered V p) :
    ∀ᵐ t ∂volume.restrict G.I.carrier, ∃ i,
      V.field i (G.graphMap p t) ≠ 0 ∧
      Family.wedge (V.field i (G.graphMap p t)) (1, deriv (fun s => G.γ s p) t) = 0 := by
  let B := {x : Plane | ¬ ∃ i, V.field i x ≠ 0 ∧
    Family.wedge (V.field i x) (1, deriv (fun s => G.γ s p) x.1) = 0}
  have hb : (Measure.hausdorffMeasure 1) (G.curve p ∩ B) = 0 := by
    have he := (ae_restrict_iff' (G.curve_isCompact ha p hp).measurableSet).mp hV
    have hz := ae_iff.mp he
    convert hz using 1
    congr 1
    ext x
    simp only [B, mem_inter_iff, mem_setOf_eq, Classical.not_imp]
  have ht : volume (G.hitTimes p B) = 0 := by
    by_contra hn
    have hpos := (G.smooth_graph_positive_iff ha p hp B).mpr (pos_iff_ne_zero.mpr hn)
    exact hpos.ne' hb
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  apply ae_iff.mpr
  convert ht using 1
  congr 1
  ext t
  simp only [Family.hitTimes, B, Family.graphMap, Interval.carrier, mem_setOf_eq, Classical.not_imp]

namespace IntermediateModel
variable {d : ℕ} {G : Family 2 d} (M : IntermediateModel G)

def parameter (x : ℝ) (w : Aux (d + 1)) : Parameters 2 d :=
  intermediateCoordinates d M.j (M.F (x, w))

theorem parameter_mem (x : ℝ) (hx : x ∈ Metric.ball M.data.base.1 M.data.radius)
    (w : Aux (d + 1)) (hw : w ∈ Metric.ball M.data.base.2 M.data.radius) :
    M.parameter x w ∈ G.W :=
  M.target_subset _ (M.F.map_source (M.source_eq ▸ ⟨hx, hw⟩))

theorem parameter_center (x : ℝ) (w : Aux (d + 1)) :
    (M.parameter x w).1 = centerCoordinates M.j (x, M.data.κ (x, w)) := by
  ext i
  change (if i = M.j then (M.F (x, w)).2 0 else (M.F (x, w)).1) = _
  rw [centerCoordinates_apply, M.κ_eq, M.keep_first]

theorem hitTimes_eq (x : ℝ) (hx : x ∈ Metric.ball M.data.base.1 M.data.radius)
    (w : Aux (d + 1)) (hw : w ∈ Metric.ball M.data.base.2 M.data.radius) (E : Set Plane) :
    G.hitTimes (M.parameter x w) E = M.data.hitTimes w E := by
  ext t
  have hi : M.data.I.carrier = G.I.carrier := congrArg Interval.carrier M.interval_eq
  by_cases ht : t ∈ G.I.carrier
  · have he := M.identity (x, w) (M.source_eq ▸ ⟨hx, hw⟩) t ht
    change G.γ t (M.parameter x w) = M.data.h t w at he
    simp only [Family.hitTimes, Family.graphMap, ProjectionModel.hitTimes, hi, mem_setOf_eq, he]
  · simp [Family.hitTimes, ProjectionModel.hitTimes, hi, ht]

theorem covered_implies_timeCovered (ha : G.IsAnalytic) (V : Family.Foliations)
    (x : ℝ) (hx : x ∈ Metric.ball M.data.base.1 M.data.radius)
    (w : Aux (d + 1)) (hw : w ∈ Metric.ball M.data.base.2 M.data.radius)
    (hV : G.Covered V (M.parameter x w)) : M.data.TimeCovered V w := by
  have htimes := G.covered_by_times ha.isSmooth (M.parameter x w) (M.parameter_mem x hx w hw) V hV
  have hi : M.data.I.carrier = G.I.carrier := congrArg Interval.carrier M.interval_eq
  have he : EqOn (fun t => G.γ t (M.parameter x w)) (fun t => M.data.h t w) G.I.carrier :=
    fun t ht => M.identity (x, w) (M.source_eq ▸ ⟨hx, hw⟩) t ht
  have hd := (he.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have hends : ∀ᵐ t ∂volume.restrict G.I.carrier, t ≠ G.I.left ∧ t ≠ G.I.right := by
    apply ae_restrict_of_ae
    filter_upwards [volume.ae_ne G.I.left, volume.ae_ne G.I.right]
      with t hl hr
    exact ⟨hl, hr⟩
  rw [ProjectionModel.TimeCovered, hi]
  filter_upwards [htimes, hends, ae_restrict_mem measurableSet_Icc] with t ht hte htI
  have htO : t ∈ Ioo G.I.left G.I.right :=
    ⟨lt_of_le_of_ne htI.1 hte.1.symm, lt_of_le_of_ne htI.2 hte.2⟩
  simpa only [Family.graphMap, he htI, hd htO] using ht

include M in
theorem admitsNikodym (hP : ProjectionConstructionInput) (hd : 0 < d)
    (ha : G.IsAnalytic) : G.AdmitsNikodym := by
  obtain ⟨E, hE, hE0, htrace⟩ := hP d hd M.data
  obtain ⟨F, hFsub, hF, hFpos⟩ := positivePart_image_coordinates (centerCoordinates M.j) _ htrace
  apply (G.admitsNikodym_iff_byTimes ha.isSmooth).mpr
  refine ⟨E, F, hE, hF, hE0, hFpos, ?_⟩
  intro z hz
  obtain ⟨c, ⟨x, hx, w, hw, hc, ht⟩, hcz⟩ := hFsub hz
  subst c
  let p := M.parameter x w
  have hp := M.parameter_mem x hx w hw
  have hpz : p.1 = z := (M.parameter_center x w).trans hcz
  refine ⟨p.2, hpz ▸ hp, ?_⟩
  have he := M.hitTimes_eq x hx w hw E
  rw [← he] at ht
  change 0 < volume (G.hitTimes (p.1, p.2) E) at ht
  rwa [hpz] at ht

include M in
theorem localReuseNotCovered (hP : ProjectionAvoidanceInput) (hd : 0 < d)
    (hW : IsOpen G.W) (ha : G.IsAnalytic) (hr : ConstantRanks G d (d + 1)) :
    G.LocalReuseNotCovered := by
  intro V
  apply (positivePart_image_coordinates (centerCoordinates M.j) _ (hP d hd M.data V)).mono
  rintro z ⟨c, ⟨x, hx, w, hw, hc, hnc⟩, hcz⟩
  subst c
  let p := M.parameter x w
  have hp := M.parameter_mem x hx w hw
  have hpz : p.1 = z := (M.parameter_center x w).trans hcz
  have hl := full_intermediate_locallyReused G hW ha
    (fun p hp => (hr p hp).1) (fun p hp => (hr p hp).2) p hp
  have hn : ¬ G.Covered V p := fun hv => hnc (M.covered_implies_timeCovered ha V x hx w hw hv)
  exact ⟨p.2, hpz ▸ hl, hpz ▸ hn⟩

end IntermediateModel
end PlanarNikodym
