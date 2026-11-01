import PlanarNikodym.Core.ReuseBasics

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

theorem Family.covered_of_finite_exceptions {d : ℕ} (G : Family 2 d) (ha : G.IsSmooth)
    (p : Parameters 2 d) (hp : p ∈ G.W) (V : Family.Foliations) (Z : Set ℝ) (hZ : Z.Finite)
    (h : ∀ t ∈ G.I.carrier, t ∉ Z → ∃ i, V.field i (G.graphMap p t) ≠ 0 ∧
      Family.wedge (V.field i (G.graphMap p t)) (1, deriv (fun r => G.γ r p) t) = 0) :
    G.Covered V p := by
  letI := Measure.noAtoms_hausdorff (X := Plane) (d := 1) (by norm_num)
  have hz : (Measure.hausdorffMeasure 1) (G.graphMap p '' Z) = 0 :=
    (hZ.image _).countable.measure_zero _
  have hn : ∀ᵐ x ∂Measure.hausdorffMeasure 1, x ∉ G.graphMap p '' Z :=
    compl_mem_ae_iff.mpr hz
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (G.curve_isCompact ha p hp).measurableSet] with x hx hxc
  obtain ⟨t, ht, rfl⟩ := hxc
  have htZ : t ∉ Z := fun hz => hx ⟨t, hz, rfl⟩
  simpa only [Family.graphMap] using h t ht htZ

theorem Family.values_eq_of_curve_eq {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (p : Parameters 2 d) (q : Parameters 2 e) (he : G.curve p = H.curve q) :
    ∀ t ∈ G.I.carrier, G.γ t p = H.γ t q := by
  intro t ht
  have hm : G.graphMap p t ∈ H.curve q := he ▸ Set.mem_image_of_mem _ ht
  obtain ⟨s, _, hs⟩ := hm
  have hst : s = t := congrArg Prod.fst hs
  subst s
  exact (congrArg Prod.snd hs).symm

/-- Coverage depends on the curve image. Equality of derivatives is only
needed in the interior; the two endpoint graph points form a null set. -/
theorem Family.covered_of_curve_eq {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (ha : G.IsSmooth) (p : Parameters 2 d) (hp : p ∈ G.W)
    (q : Parameters 2 e) (V : Family.Foliations) (he : G.curve p = H.curve q)
    (hH : H.Covered V q) : G.Covered V p := by
  letI := Measure.noAtoms_hausdorff (X := Plane) (d := 1) (by norm_num)
  let Z := G.graphMap p '' ({G.I.left, G.I.right} : Set ℝ)
  have hZ : (Measure.hausdorffMeasure 1) Z = 0 :=
    (((Set.finite_singleton G.I.right).insert G.I.left).image _).countable.measure_zero _
  have hn : ∀ᵐ x ∂Measure.hausdorffMeasure 1, x ∉ Z := compl_mem_ae_iff.mpr hZ
  have hd : Set.EqOn (deriv (fun t => G.γ t p)) (deriv (fun t => H.γ t q))
      (Ioo G.I.left G.I.right) :=
    (show Set.EqOn (fun t => G.γ t p) (fun t => H.γ t q) (Ioo G.I.left G.I.right) from
      fun t ht => G.values_eq_of_curve_eq H p q he t ⟨ht.1.le, ht.2.le⟩).deriv isOpen_Ioo
  have hHC : ∀ᵐ x ∂(Measure.hausdorffMeasure 1).restrict (G.curve p),
      ∃ i, V.field i x ≠ 0 ∧ Family.wedge (V.field i x) (1, deriv (fun t => H.γ t q) x.1) = 0 := by
    simpa only [Family.Covered, he] using hH
  filter_upwards [hHC, ae_restrict_of_ae hn,
    ae_restrict_mem (G.curve_isCompact ha p hp).measurableSet] with x hx hxZ hxc
  obtain ⟨t, ht, rfl⟩ := hxc
  have htL : t ≠ G.I.left := fun he => hxZ ⟨t, by simp [he], rfl⟩
  have htR : t ≠ G.I.right := fun he => hxZ ⟨t, by simp [he], rfl⟩
  have htO : t ∈ Ioo G.I.left G.I.right :=
    ⟨lt_of_le_of_ne ht.1 htL.symm, lt_of_le_of_ne ht.2 htR⟩
  simpa only [Family.graphMap, hd htO] using hx

def Family.Foliations.iUnion (V : ℕ → Family.Foliations) : Family.Foliations where
  field i := (V (Nat.unpair i).1).field (Nat.unpair i).2
  smooth i := (V (Nat.unpair i).1).smooth (Nat.unpair i).2

theorem Family.covered_iUnion {d : ℕ} (G : Family 2 d) (V : ℕ → Family.Foliations)
    (n : ℕ) (p : Parameters 2 d) (h : G.Covered (V n) p) :
    G.Covered (Family.Foliations.iUnion V) p := by
  filter_upwards [h] with x hx
  obtain ⟨i, hi, he⟩ := hx
  exact ⟨Nat.pair n i, by simpa [Family.Foliations.iUnion] using hi,
    by simpa [Family.Foliations.iUnion] using he⟩

theorem Family.covered_of_equal_time_function {d : ℕ} (G : Family 2 d) (ha : G.IsSmooth)
    (p : Parameters 2 d) (hp : p ∈ G.W) (V : Family.Foliations) (f : ℝ → ℝ)
    (he : ∀ t ∈ G.I.carrier, G.γ t p = f t) (Z : Set ℝ) (hZ : Z.Finite)
    (h : ∀ t ∈ G.I.carrier, t ∉ Z → ∃ i, V.field i (t, f t) ≠ 0 ∧
      Family.wedge (V.field i (t, f t)) (1, deriv f t) = 0) : G.Covered V p := by
  apply G.covered_of_finite_exceptions ha p hp V (Z ∪ {G.I.left, G.I.right})
    (hZ.union ((Set.finite_singleton G.I.right).insert G.I.left))
  intro t ht htz
  have htZ : t ∉ Z := fun h => htz (Or.inl h)
  have htL : t ≠ G.I.left := fun h => htz (Or.inr (by simp [h]))
  have htR : t ≠ G.I.right := fun h => htz (Or.inr (by simp [h]))
  have hd : Set.EqOn (deriv (fun t => G.γ t p)) (deriv f) (Ioo G.I.left G.I.right) :=
    (show Set.EqOn (fun t => G.γ t p) f (Ioo G.I.left G.I.right) from
      fun t ht => he t ⟨ht.1.le, ht.2.le⟩).deriv isOpen_Ioo
  simpa only [Family.graphMap, he t ht,
    hd ⟨lt_of_le_of_ne ht.1 htL.symm, lt_of_le_of_ne ht.2 htR⟩] using h t ht htZ

end PlanarNikodym
