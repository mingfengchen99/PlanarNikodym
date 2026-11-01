import PlanarNikodym.Analysis.Maximal.GeneralSmoothAnalysis

/-! Closed time endpoints are removed by a genuine countable family of
compact interior intervals. No extension of the ambient defining function
outside its original smooth domain is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PlanarNikodym

/-- Rational closed intervals strictly inside the original interval. -/
def InteriorIntervalIndex (I : Interval) :=
  {q : ℚ × ℚ // I.left < (q.1 : ℝ) ∧ q.1 < q.2 ∧ (q.2 : ℝ) < I.right}

instance (I : Interval) : Countable (InteriorIntervalIndex I) := by
  unfold InteriorIntervalIndex
  infer_instance

def interiorInterval (I : Interval) (i : InteriorIntervalIndex I) : Interval :=
  ⟨i.val.1, i.val.2, by exact_mod_cast i.property.2.1⟩

theorem interiorInterval_subset (I : Interval) (i : InteriorIntervalIndex I) :
    (interiorInterval I i).carrier ⊆ Ioo I.left I.right :=
  Icc_subset_Ioo i.property.1 i.property.2.2

theorem iUnion_interiorInterval (I : Interval) :
    (⋃ i : InteriorIntervalIndex I, (interiorInterval I i).carrier) =
      Ioo I.left I.right := by
  apply Subset.antisymm
  · exact iUnion_subset (interiorInterval_subset I)
  · intro t ht
    obtain ⟨a, ha, hat⟩ := exists_rat_btwn ht.1
    obtain ⟨b, htb, hb⟩ := exists_rat_btwn ht.2
    have hab : a < b := by exact_mod_cast hat.trans htb
    exact mem_iUnion.mpr ⟨⟨(a, b), ha, hab, hb⟩, hat.le, htb.le⟩

theorem Family.contDiffAt_of_isSmooth_interior {n d : ℕ} (G : Family n d)
    (hW : IsOpen G.W) (hG : G.IsSmooth) {x : ℝ × Parameters n d}
    (hx : x ∈ Ioo G.I.left G.I.right ×ˢ G.W) :
    ContDiffAt ℝ ∞ (fun y : ℝ × Parameters n d => G.γ y.1 y.2) x := by
  apply hG.contDiffAt
  exact mem_of_superset ((isOpen_Ioo.prod hW).mem_nhds hx)
    (prod_mono Ioo_subset_Icc_self Subset.rfl)

theorem Family.interiorInterval_smooth_at {n d : ℕ} (G : Family n d)
    (hW : IsOpen G.W) (hG : G.IsSmooth) (i : InteriorIntervalIndex G.I) :
    ∀ x ∈ (interiorInterval G.I i).carrier ×ˢ G.W,
      ContDiffAt ℝ ∞ (fun y : ℝ × Parameters n d => G.γ y.1 y.2) x := by
  intro x hx
  exact G.contDiffAt_of_isSmooth_interior hW hG
    ⟨interiorInterval_subset G.I i hx.1, hx.2⟩

/-- Every positive length incidence survives on a compact interior
interval. This uses only that the two original endpoints have measure zero. -/
theorem Family.hitTimes_pos_iff_interiorInterval {n d : ℕ} (G : Family n d)
    (p : Parameters n d) (E : Set Plane) :
    0 < volume (G.hitTimes p E) ↔
      ∃ i : InteriorIntervalIndex G.I,
        0 < volume ((G.withInterval (interiorInterval G.I i)).hitTimes p E) := by
  constructor
  · intro hp
    by_contra hn
    have hnull (i : InteriorIntervalIndex G.I) :
        volume ((G.withInterval (interiorInterval G.I i)).hitTimes p E) = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp (fun hi => hn ⟨i, hi⟩))
    have hs : G.hitTimes p E ⊆ {G.I.left, G.I.right} ∪
        ⋃ i : InteriorIntervalIndex G.I,
          (G.withInterval (interiorInterval G.I i)).hitTimes p E := by
      intro t ht
      by_cases hl : t = G.I.left
      · exact Or.inl (by simp [hl])
      by_cases hr : t = G.I.right
      · exact Or.inl (by simp [hr])
      have hti : t ∈ Ioo G.I.left G.I.right :=
        ⟨lt_of_le_of_ne ht.1.1 (Ne.symm hl), lt_of_le_of_ne ht.1.2 hr⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp ((iUnion_interiorInterval G.I).symm ▸ hti)
      exact Or.inr (mem_iUnion.mpr ⟨i, hi, ht.2⟩)
    exact hp.ne' (measure_mono_null hs (measure_union_null
      ((show ({G.I.left, G.I.right} : Set ℝ).Finite by simp).countable.measure_zero volume)
      (measure_iUnion_null hnull)))
  · rintro ⟨i, hi⟩
    apply hi.trans_le (measure_mono ?_)
    intro t ht
    exact ⟨Ioo_subset_Icc_self (interiorInterval_subset G.I i ht.1), ht.2⟩

theorem Family.timeIncidenceCenters_eq_iUnion_interiorInterval {d : ℕ}
    (G : Family 2 d) (U : Set (Parameters 2 d)) (E : Set Plane) :
    G.timeIncidenceCenters U E = ⋃ i : InteriorIntervalIndex G.I,
      (G.withInterval (interiorInterval G.I i)).timeIncidenceCenters U E := by
  ext z
  simp only [Family.timeIncidenceCenters, mem_setOf_eq, mem_iUnion]
  constructor
  · rintro ⟨u, hu, hp⟩
    obtain ⟨i, hi⟩ := (G.hitTimes_pos_iff_interiorInterval (z, u) E).mp hp
    exact ⟨i, u, hu, hi⟩
  · rintro ⟨i, u, hu, hp⟩
    exact ⟨u, hu, (G.hitTimes_pos_iff_interiorInterval (z, u) E).mpr ⟨i, hp⟩⟩

/-- Interior interval exclusion suffices for the original closed interval,
without any analytic premise or assumption outside the interval. -/
theorem Family.timeIncidenceCenters_null_of_interiorIntervals {d : ℕ}
    (G : Family 2 d) (U : Set (Parameters 2 d)) (E : Set Plane)
    (h : ∀ i : InteriorIntervalIndex G.I,
      volume ((G.withInterval (interiorInterval G.I i)).timeIncidenceCenters U E) = 0) :
    volume (G.timeIncidenceCenters U E) = 0 := by
  rw [G.timeIncidenceCenters_eq_iUnion_interiorInterval U E]
  exact measure_iUnion_null h

end PlanarNikodym
