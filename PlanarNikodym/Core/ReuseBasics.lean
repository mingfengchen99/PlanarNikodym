import PlanarNikodym.Reduction.FamilyReduction
import PlanarNikodym.Core.GraphMeasure
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Set Filter MeasureTheory Module
open scoped Topology ContDiff
namespace PlanarNikodym

theorem HasPositivePart.mono {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S T : Set X} (h : HasPositivePart μ S) (hST : S ⊆ T) : HasPositivePart μ T := by
  obtain ⟨A, hA, hm, hp⟩ := h
  exact ⟨A, hA.trans hST, hm, hp⟩

theorem HasPositivePart.nonempty {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S : Set X} (h : HasPositivePart μ S) : S.Nonempty := by
  obtain ⟨A, hA, _, hp⟩ := h
  exact (MeasureTheory.nonempty_of_measure_ne_zero hp.ne').mono hA

abbrev Family.restrictTo {n d : ℕ} (G : Family n d) (U : Set (Parameters n d)) : Family n d :=
  { G with W := U }

theorem Family.IsAnalytic.isSmooth {n d : ℕ} {G : Family n d} (ha : G.IsAnalytic) :
    G.IsSmooth := ha.contDiffOn_of_completeSpace

theorem Family.IsAnalytic.restrictTo {n d : ℕ} {G : Family n d} (ha : G.IsAnalytic)
    {U : Set (Parameters n d)} (hU : U ⊆ G.W) : (G.restrictTo U).IsAnalytic :=
  fun p hp => ha p ⟨hp.1, hU hp.2⟩

theorem Family.mem_centersOf {d : ℕ} (G : Family 2 d) (β : Set Plane) (z : Base 2) :
    z ∈ G.centersOf β ↔ ∃ u, (z, u) ∈ G.W ∧ G.curve (z, u) = β := by
  constructor
  · rintro ⟨⟨z', u⟩, ⟨hp, he⟩, hz⟩
    change z' = z at hz
    subst z'
    exact ⟨u, hp, he⟩
  · rintro ⟨u, hp, he⟩
    exact ⟨(z, u), ⟨hp, he⟩, rfl⟩

theorem Family.centersOf_mono {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (h : ∀ z, G.curvesAtOn G.W z ⊆ H.curvesAtOn H.W z) (β : Set Plane) :
    G.centersOf β ⊆ H.centersOf β := by
  intro z hz
  exact (H.mem_centersOf β z).mpr (h z ((G.mem_centersOf β z).mp hz))

theorem Family.hasMassiveCurveReuse_mono {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (h : ∀ z, G.curvesAtOn G.W z ⊆ H.curvesAtOn H.W z)
    (hG : G.HasMassiveCurveReuse) : H.HasMassiveCurveReuse := by
  obtain ⟨β, hβ⟩ := hG
  exact ⟨β, hβ.mono (G.centersOf_mono H h β)⟩

theorem Family.admitsNikodym_mono {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (h : ∀ z, G.curvesAtOn G.W z ⊆ H.curvesAtOn H.W z)
    (hG : G.AdmitsNikodym) : H.AdmitsNikodym := by
  obtain ⟨E, F, hE, hF, hE0, hFp, hf⟩ := hG
  refine ⟨E, F, hE, hF, hE0, hFp, ?_⟩
  intro z hz
  obtain ⟨u, hu, hpos⟩ := hf z hz
  obtain ⟨v, hv, he⟩ := h z ⟨u, hu, rfl⟩
  exact ⟨v, hv, he ▸ hpos⟩

theorem Family.curve_isCompact {n d : ℕ} (G : Family n d) (ha : G.IsSmooth)
    (p : Parameters n d) (hp : p ∈ G.W) : IsCompact (G.curve p) := by
  obtain ⟨K, hK⟩ := G.smooth_graph_lipschitz ha p hp
  exact isCompact_Icc.image_of_continuousOn hK.continuousOn

theorem Family.curve_volume_zero {n d : ℕ} (G : Family n d) (ha : G.IsSmooth)
    (p : Parameters n d) (hp : p ∈ G.W) : volume (G.curve p) = 0 := by
  have hm := (G.curve_isCompact ha p hp).measurableSet
  change (volume.prod volume) (G.curve p) = 0
  apply Measure.measure_prod_null_of_ae_null hm
  apply Filter.Eventually.of_forall
  intro t
  apply measure_mono_null (t := {G.γ t p})
  · rintro y ⟨s, hs, he⟩
    have hst : s = t := congrArg Prod.fst he
    subst s
    exact Set.mem_singleton_iff.mpr (congrArg Prod.snd he).symm
  · exact measure_singleton _

theorem Family.curve_hausdorff_pos {n d : ℕ} (G : Family n d) (ha : G.IsSmooth)
    (p : Parameters n d) (hp : p ∈ G.W) : 0 < Measure.hausdorffMeasure 1 (G.curve p) := by
  have hh : G.hitTimes p (G.curve p) = G.I.carrier := by
    ext t
    exact ⟨fun h => h.1, fun ht => ⟨ht, ⟨t, ht, rfl⟩⟩⟩
  have hi : 0 < volume G.I.carrier := by
    rw [Interval.carrier, Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr G.I.nondegenerate)
  have h := (G.smooth_graph_positive_iff ha p hp (G.curve p)).mpr (hh ▸ hi)
  simpa only [inter_self] using h

/-- A massively reused curve itself is a Borel null Nikodym witness. -/
theorem Family.admitsNikodym_of_hasMassiveCurveReuse {d : ℕ} (G : Family 2 d)
    (ha : G.IsSmooth) (h : G.HasMassiveCurveReuse) : G.AdmitsNikodym := by
  obtain ⟨β, A, hA, hm, hpos⟩ := h
  obtain ⟨z, hz⟩ := MeasureTheory.nonempty_of_measure_ne_zero hpos.ne'
  obtain ⟨u, hu, he⟩ := (G.mem_centersOf β z).mp (hA hz)
  have hb : MeasurableSet β := he ▸ (G.curve_isCompact ha (z, u) hu).measurableSet
  have hb0 : volume β = 0 := he ▸ G.curve_volume_zero ha (z, u) hu
  have hbp : 0 < Measure.hausdorffMeasure 1 β := he ▸ G.curve_hausdorff_pos ha (z, u) hu
  refine ⟨β, A, hb, hm, hb0, hpos, ?_⟩
  intro z hz
  obtain ⟨u, hu, he⟩ := (G.mem_centersOf β z).mp (hA hz)
  exact ⟨u, hu, by simpa only [he, inter_self] using hbp⟩

end PlanarNikodym
