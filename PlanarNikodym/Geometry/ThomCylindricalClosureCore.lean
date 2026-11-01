import PlanarNikodym.Geometry.ThomClosureCompactFiber

/-! The weak-sign closure step in the higher-dimensional Thom argument.
The compact-section hypothesis is isolated here and constructed for fixed
monic normalizations in `ThomMonicCylindricalClosure`. -/
noncomputable section
open Set Filter Polynomial
open scoped Topology
namespace PlanarNikodym

def polynomialThomCylinder {E ι : Type*} (C : Set E)
    (P : E → ι → ℝ[X]) (s : ι → Fin 3) : Set (E × ℝ) :=
  {z | z.1 ∈ C ∧ z.2 ∈ polynomialThomFamilyCell false (P z.1) s}

theorem polynomialThomFamilyCell_strong_nonempty_of_weak_not_subsingleton
    {ι : Type*} [Fintype ι] (P : ι → ℝ[X]) (s : ι → Fin 3)
    (hder : ∀ j, ∃ k, (P j).derivative = P k)
    (hn : ∀ j, s j ≠ 1 → P j ≠ 0)
    (hns : ¬ (polynomialThomFamilyCell true P s).Subsingleton) :
    (polynomialThomFamilyCell false P s).Nonempty := by
  classical
  let Z : Set ℝ := ⋃ j, {t | s j ≠ 1 ∧ (P j).eval t = 0}
  have hZ : Z.Finite := by
    apply Set.finite_iUnion
    intro j
    by_cases hs : s j = 1
    · simpa only [hs, ne_eq, not_true_eq_false, false_and, setOf_false] using finite_empty
    · exact (Polynomial.finite_setOf_isRoot (hn j hs)).subset (fun _ ht => ht.2)
  by_contra hne
  apply hns
  apply ordConnected_subsingleton_of_finite
    (polynomialThomFamilyCell_ordConnected true P hder s)
  apply hZ.subset
  intro t ht
  by_contra htZ
  apply hne
  refine ⟨t, fun j => polynomialSignCondition_strict_of_weak (ht j) ?_⟩
  intro hs hz
  exact htZ (mem_iUnion.mpr ⟨j, hs, hz⟩)

theorem polynomialThomCylinder_closure_subset_weak
    {E ι : Type*} [TopologicalSpace E] (C V : Set E)
    (P : E → ι → ℝ[X]) (s : ι → Fin 3)
    (hc : ∀ x ∈ V, ∀ t j,
      ContinuousAt (fun z : E × ℝ => (P z.1 j).eval z.2) (x, t))
    {z : E × ℝ} (hz : z ∈ closure (polynomialThomCylinder C P s)) (hzV : z.1 ∈ V) :
    z.1 ∈ closure C ∧ z.2 ∈ polynomialThomFamilyCell true (P z.1) s := by
  refine ⟨?_, fun j => ?_⟩
  · exact continuous_fst.continuousAt.continuousWithinAt.mem_closure hz
      (fun _ hw => hw.1)
  · have hw : (P z.1 j).eval z.2 ∈ closure {r | polynomialSignCondition true (s j) r} :=
      (hc z.1 hzV z.2 j).continuousWithinAt.mem_closure hz
        (fun _ hw => polynomialSignCondition_weaken (hw.2 j))
    rwa [(isClosed_polynomialWeakSignCondition (s j)).closure_eq] at hw

private theorem isOpen_strict_real_sign (s : Fin 3) (hs : s ≠ 1) :
    IsOpen {r : ℝ | polynomialSignCondition false s r} := by
  fin_cases s
  · simpa [polynomialSignCondition, oneDimensionalSign_eq_zero, Set.Iio] using
      (isOpen_Iio : IsOpen (Iio (0 : ℝ)))
  · exact False.elim (hs rfl)
  · simpa [polynomialSignCondition, oneDimensionalSign_eq_two, Set.Ioi] using
      (isOpen_Ioi : IsOpen (Ioi (0 : ℝ)))

/-- The exact cylindrical weak-sign closure formula. No connectedness of
the base or choice of analytic root branches is assumed in this step. -/
theorem polynomialThomCylinder_closure_of_compact_sections
    {E ι : Type*} [TopologicalSpace E] [Fintype ι]
    (C V : Set E) (P : E → ι → ℝ[X]) (s : ι → Fin 3)
    (hV : IsOpen V) (hCV : C ⊆ V)
    (hc : ∀ x ∈ V, ∀ t j,
      ContinuousAt (fun z : E × ℝ => (P z.1 j).eval z.2) (x, t))
    (hder : ∀ x ∈ V, ∀ j, ∃ k, (P x j).derivative = P x k)
    (hstable : ∀ j, (∀ x ∈ V, P x j = 0) ∨ (∀ x ∈ V, P x j ≠ 0))
    (hne : ∀ x ∈ C, (polynomialThomFamilyCell false (P x) s).Nonempty)
    (hcompact : ∀ x ∈ closure C ∩ V, ∃ (U : Set E) (R : ℝ),
      IsOpen U ∧ x ∈ U ∧ ∀ y ∈ C ∩ U,
        ∃ t ∈ Icc (-R) R, t ∈ polynomialThomFamilyCell false (P y) s) :
    closure (polynomialThomCylinder C P s) ∩ (V ×ˢ univ) =
      {z | z.1 ∈ closure C ∩ V ∧ z.2 ∈ polynomialThomFamilyCell true (P z.1) s} := by
  classical
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    have hw := polynomialThomCylinder_closure_subset_weak C V P s hc hz hzV.1
    exact ⟨⟨hw.1, hzV.1⟩, hw.2⟩
  · rintro ⟨hx, ht⟩
    refine ⟨?_, hx.2, mem_univ _⟩
    obtain ⟨U, R, hU, hxU, hsection⟩ := hcompact z.1 hx
    have hxCU := mem_closure_inter_of_isOpen hx.1 hU hxU
    obtain ⟨a, _, ha⟩ := exists_mem_closure_fiber_of_compact_section
      (polynomialThomCylinder C P s) (C ∩ U) z.1 (Icc (-R) R) isCompact_Icc hxCU (by
        intro y hy
        obtain ⟨t, htK, htS⟩ := hsection y hy
        exact ⟨t, htK, hy.1, htS⟩)
    have haW := (polynomialThomCylinder_closure_subset_weak C V P s hc ha hx.2).2
    by_cases hsub : (polynomialThomFamilyCell true (P z.1) s).Subsingleton
    · have he : z.2 = a := hsub ht haW
      change (z.1, z.2) ∈ closure (polynomialThomCylinder C P s)
      rwa [he]
    · have hweakConn := polynomialThomFamilyCell_ordConnected true (P z.1) (hder z.1 hx.2) s
      have heq (j : ι) (hs : s j = 1) : ∀ x ∈ V, P x j = 0 := by
        rcases hstable j with hj | hj
        · exact hj
        · apply False.elim
          apply hsub
          apply ordConnected_subsingleton_of_finite hweakConn
          apply (Polynomial.finite_setOf_isRoot (hj z.1 hx.2)).subset
          intro t ht'
          simpa [polynomialSignCondition, hs] using ht' j
      obtain ⟨y, hy⟩ := (show (closure C).Nonempty from ⟨z.1, hx.1⟩).of_closure
      obtain ⟨b, hb⟩ := hne y hy
      have hnonzero (j : ι) (hs : s j ≠ 1) : P z.1 j ≠ 0 := by
        rcases hstable j with hj | hj
        · exfalso
          apply polynomialSignCondition_ne_zero hs (hb j)
          simp [hj y (hCV hy)]
        · exact hj z.1 hx.2
      have hsne := polynomialThomFamilyCell_strong_nonempty_of_weak_not_subsingleton
        (P z.1) s (hder z.1 hx.2) hnonzero hsub
      have hstrict (t : ℝ) (htS : t ∈ polynomialThomFamilyCell false (P z.1) s) :
          (z.1, t) ∈ closure (polynomialThomCylinder C P s) := by
        have hevent : ∀ᶠ x in 𝓝 z.1,
            ∀ j, polynomialSignCondition false (s j) ((P x j).eval t) := by
          apply Filter.eventually_all.mpr
          intro j
          by_cases hs : s j = 1
          · filter_upwards [hV.mem_nhds hx.2] with x hxV
            simp [polynomialSignCondition, hs, heq j hs x hxV, oneDimensionalSign]
          · have hct : ContinuousAt (fun x => (P x j).eval t) z.1 :=
              ContinuousAt.comp (f := fun x : E => (x, t))
                (g := fun w : E × ℝ => (P w.1 j).eval w.2)
                (hc z.1 hx.2 t j) (continuousAt_id.prodMk continuousAt_const)
            exact hct.preimage_mem_nhds ((isOpen_strict_real_sign (s j) hs).mem_nhds (htS j))
        obtain ⟨N, hNsub, hN, hxN⟩ := mem_nhds_iff.mp hevent
        have hxCN := mem_closure_inter_of_isOpen hx.1 hN hxN
        have him : (z.1, t) ∈ closure ((fun x : E => (x, t)) '' (C ∩ N)) :=
          mem_closure_image (continuous_id.prodMk continuous_const).continuousAt hxCN
        apply closure_mono (s := (fun x : E => (x, t)) '' (C ∩ N)) ?_ him
        rintro w ⟨x, hxCN', rfl⟩
        exact ⟨hxCN'.1, hNsub hxCN'.2⟩
      have hclosed : IsClosed {t : ℝ | (z.1, t) ∈ closure (polynomialThomCylinder C P s)} :=
        isClosed_closure.preimage (continuous_const.prodMk continuous_id)
      have hclosure := closure_minimal hstrict hclosed
      rw [polynomialThomFamilyCell_closure (P z.1) (hder z.1 hx.2) s hsne] at hclosure
      exact hclosure ht

end PlanarNikodym
