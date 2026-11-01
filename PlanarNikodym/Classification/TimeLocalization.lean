import PlanarNikodym.Geometry.IncidenceCenters
import PlanarNikodym.Geometry.AnalyticZeros

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym

abbrev Family.withInterval {n d : ℕ} (G : Family n d) (J : Interval) : Family n d :=
  { G with I := J }

def Family.timeIncidenceCenters {d : ℕ} (G : Family 2 d) (U : Set (Parameters 2 d))
    (E : Set Plane) : Set (Base 2) :=
  {z | ∃ u, (z, u) ∈ U ∧ 0 < volume (G.hitTimes (z, u) E)}

theorem Family.timeIncidenceCenters_eq {d : ℕ} (G : Family 2 d) (ha : G.IsSmooth)
    (U : Set (Parameters 2 d)) (hU : U ⊆ G.W) (E : Set Plane) :
    G.timeIncidenceCenters U E = G.incidenceCenters U E := by
  ext z
  constructor <;> rintro ⟨u, hu, hp⟩ <;> refine ⟨u, hu, ?_⟩
  · exact (G.smooth_graph_positive_iff ha (z, u) (hU hu) E).mpr hp
  · exact (G.smooth_graph_positive_iff ha (z, u) (hU hu) E).mp hp

/-- Countable time/parameter localization. Finite exceptional times on every
curve can be discarded before applying a local exclusion theorem. No
measurability of the centre projections is required. -/
theorem time_incidence_null_of_regular_patches {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (D : ℝ × Parameters 2 d → ℝ)
    (hD : ContinuousOn D (G.I.carrier ×ˢ G.W))
    (hfinite : ∀ p ∈ G.W, {t | t ∈ G.I.carrier ∧ D (t, p) = 0}.Finite)
    (E : Set Plane)
    (hlocal : ∀ (J : Interval), J.carrier ⊆ G.I.carrier →
      ∀ U : Set (Parameters 2 d), IsOpen U → U ⊆ G.W →
      (∀ t ∈ J.carrier, ∀ p ∈ U, D (t, p) ≠ 0) →
      volume ((G.withInterval J).timeIncidenceCenters U E) = 0) :
    volume (G.timeIncidenceCenters G.W E) = 0 := by
  classical
  let S := {x : ℝ × Parameters 2 d |
    x.1 ∈ Ioo G.I.left G.I.right ∧ x.2 ∈ G.W ∧ D x ≠ 0}
  have hpatch (x : S) : ∃ J : Interval, ∃ U : Set (Parameters 2 d),
      IsOpen U ∧ x.1.1 ∈ Ioo J.left J.right ∧ x.1.2 ∈ U ∧
      J.carrier ⊆ G.I.carrier ∧ U ⊆ G.W ∧
      ∀ t ∈ J.carrier, ∀ p ∈ U, D (t, p) ≠ 0 := by
    have hx := x.property
    have hdomain : (Ioo G.I.left G.I.right ×ˢ G.W) ∈ 𝓝 x.val :=
      (isOpen_Ioo.prod hW).mem_nhds ⟨hx.1, hx.2.1⟩
    have hDx : ContinuousAt D x.val := (hD x.val ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.1⟩).continuousAt
      (mem_of_superset hdomain (prod_mono Ioo_subset_Icc_self Subset.rfl))
    have hn : {y | y ∈ Ioo G.I.left G.I.right ×ˢ G.W ∧ D y ≠ 0} ∈ 𝓝 x.val :=
      inter_mem hdomain (hDx.eventually_ne hx.2.2)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
    let J : Interval := ⟨x.1.1 - r / 2, x.1.1 + r / 2, by linarith⟩
    let U := ball x.1.2 (r / 2)
    have hsub (t : ℝ) (ht : t ∈ J.carrier) (p : Parameters 2 d) (hp : p ∈ U) :
        (t, p) ∈ Ioo G.I.left G.I.right ×ˢ G.W ∧ D (t, p) ≠ 0 := by
      change x.1.1 - r / 2 ≤ t ∧ t ≤ x.1.1 + r / 2 at ht
      apply hball
      rw [← ball_prod_same]
      refine ⟨?_, lt_of_lt_of_le hp (by linarith : r / 2 ≤ r)⟩
      rw [mem_ball, Real.dist_eq]
      apply lt_of_le_of_lt (abs_le.mpr ⟨?_, ?_⟩) (half_lt_self hr)
      · linarith [ht.1]
      · linarith [ht.2]
    have hxU : x.1.2 ∈ U := mem_ball_self (half_pos hr)
    have hxt : x.1.1 ∈ J.carrier := ⟨by dsimp [J]; linarith, by dsimp [J]; linarith⟩
    refine ⟨J, U, isOpen_ball, ⟨by dsimp [J]; linarith, by dsimp [J]; linarith⟩,
      hxU, ?_, ?_, ?_⟩
    · intro t ht; exact ⟨(hsub t ht _ hxU).1.1.1.le, (hsub t ht _ hxU).1.1.2.le⟩
    · intro p hp; exact (hsub _ hxt p hp).1.2
    · intro t ht p hp; exact (hsub t ht p hp).2
  choose J U hU using hpatch
  obtain ⟨T, hTc, hT⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    (fun x : S => Ioo (J x).left (J x).right ×ˢ U x)
    (fun x => isOpen_Ioo.prod (hU x).1) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1, (hU ⟨x, hx⟩).2.2.1⟩)
  haveI := hTc.to_subtype
  apply measure_mono_null (t := ⋃ x : T, (G.withInterval (J x.val)).timeIncidenceCenters (U x.val) E)
  · rintro z ⟨u, hu, hp⟩
    by_contra hn
    have hnull (x : T) : volume {t | (z, u) ∈ U x.val ∧
        t ∈ (G.withInterval (J x.val)).hitTimes (z, u) E} = 0 := by
      by_cases hx : (z, u) ∈ U x.val
      · have hn' : ¬ 0 < volume ((G.withInterval (J x.val)).hitTimes (z, u) E) := by
          intro hpos
          exact hn (mem_iUnion.mpr ⟨x, u, hx, hpos⟩)
        simpa only [hx, true_and, Set.setOf_mem_eq] using nonpos_iff_eq_zero.mp (not_lt.mp hn')
      · simp [hx]
    let B := {t | t ∈ G.I.carrier ∧ D (t, (z, u)) = 0} ∪ {G.I.left, G.I.right}
    have hB : B.Finite := (hfinite (z, u) hu).union (by simp)
    have hsub : G.hitTimes (z, u) E ⊆ B ∪ ⋃ x : T,
        {t | (z, u) ∈ U x.val ∧ t ∈ (G.withInterval (J x.val)).hitTimes (z, u) E} := by
      intro t ht
      by_cases hb : t ∈ B
      · exact Or.inl hb
      · have hne : D (t, (z, u)) ≠ 0 := fun he => hb (Or.inl ⟨ht.1, he⟩)
        have htl : t ≠ G.I.left := fun he => hb (Or.inr (by simp [he]))
        have htr : t ≠ G.I.right := fun he => hb (Or.inr (by simp [he]))
        have hs : (t, (z, u)) ∈ S :=
          ⟨⟨lt_of_le_of_ne ht.1.1 htl.symm, lt_of_le_of_ne ht.1.2 htr⟩, hu, hne⟩
        obtain ⟨x, hx, htx⟩ := mem_iUnion₂.mp (hT hs)
        exact Or.inr (mem_iUnion.mpr ⟨⟨x, hx⟩, htx.2, ⟨htx.1.1.le, htx.1.2.le⟩, ht.2⟩)
    exact hp.ne' (measure_mono_null hsub
      (measure_union_null (hB.countable.measure_zero volume) (measure_iUnion_null hnull)))
  · apply measure_iUnion_null
    intro x
    exact hlocal (J x.val) (hU x.val).2.2.2.1 (U x.val) (hU x.val).1
      (hU x.val).2.2.2.2.1 (hU x.val).2.2.2.2.2

end PlanarNikodym
