import PlanarNikodym.Projection.ProjectedSweepTransfer

/-! Compact limits in the prescribed-projection construction.

This module constructs the final compact selection from nested compact
approximations. Compactness retains every prescribed centre value in
the limit, while arbitrarily small curve projection integrals force a
zero integral. The geometric finite replacement needed to produce
these approximations is a separate assertion.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PlanarNikodym

/-- Continuous images commute with decreasing intersections of compact
sets. Continuity is only required on the initial compact set. -/
theorem continuousOn_image_iInter_of_compact_antitone
    (f : Plane → ℝ) (K : ℕ → Set Plane)
    (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    (hf : ContinuousOn f (K 0)) :
    f '' (⋂ n, K n) = ⋂ n, f '' K n := by
  apply subset_antisymm
  · intro y hy
    exact mem_iInter.mpr fun n => image_mono (iInter_subset K n) hy
  · intro y hy
    let L : ℕ → Set Plane := fun n => K n ∩ f ⁻¹' {y}
    have hLc : ∀ n, IsClosed (L n) := fun n =>
      (hf.mono (hanti (Nat.zero_le n))).preimage_isClosed_of_isClosed
        (hK n).isClosed isClosed_singleton
    have hLn : ∀ n, (L n).Nonempty := by
      intro n
      obtain ⟨q, hq, he⟩ := mem_iInter.mp hy n
      exact ⟨q, hq, he⟩
    have hLanti : ∀ n, L (n + 1) ⊆ L n := fun n =>
      inter_subset_inter_left _ (hanti (Nat.le_succ n))
    have hL0 : IsCompact (L 0) :=
      (hK 0).of_isClosed_subset (hLc 0) inter_subset_left
    obtain ⟨q, hq⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        L hLanti hLn hL0 hLc
    exact ⟨q, mem_iInter.mpr (fun n => (mem_iInter.mp hq n).1),
      (mem_iInter.mp hq 0).2⟩

/-- The intersection of compact approximations is compact and therefore
Borel. Empty approximations are allowed at this purely topological step. -/
theorem isCompact_iInter_of_compact_sequence
    (K : ℕ → Set Plane) (hK : ∀ n, IsCompact (K n)) :
    IsCompact (⋂ n, K n) :=
  (hK 0).of_isClosed_subset (isClosed_iInter fun n => (hK n).isClosed)
    (iInter_subset K 0)

/-- Joint continuity on a compact time-parameter set makes its actual
scalar projection sweep compact. -/
theorem scalarProjectionSweep_isCompact
    (ψ : ℝ → Plane → ℝ) (X : Set ℝ) (K : Set Plane)
    (hX : IsCompact X) (hK : IsCompact K)
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ K)) :
    IsCompact (scalarProjectionSweep ψ X K) := by
  rw [scalarProjectionSweep_eq_image]
  exact (hX.prod hK).image_of_continuousOn (continuousOn_fst.prodMk hψ)

/-- A decreasing compact parameter sequence commutes with taking the
joint sweep. This identifies the actual intersection, not only its
measure or almost-everywhere class. -/
theorem scalarProjectionSweep_iInter_of_compact_antitone
    (ψ : ℝ → Plane → ℝ) (X : Set ℝ) (K : ℕ → Set Plane)
    (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    (hψ : ∀ x ∈ X, ContinuousOn (ψ x) (K 0)) :
    scalarProjectionSweep ψ X (⋂ n, K n) =
      ⋂ n, scalarProjectionSweep ψ X (K n) := by
  ext p
  simp only [scalarProjectionSweep, mem_setOf_eq, mem_iInter]
  constructor
  · intro hp n
    exact ⟨hp.1, image_mono (iInter_subset K n) hp.2⟩
  · intro hp
    refine ⟨(hp 0).1, ?_⟩
    rw [continuousOn_image_iInter_of_compact_antitone (ψ p.1) K hK hanti
      (hψ p.1 (hp 0).1)]
    exact mem_iInter.mpr fun n => (hp n).2

/-- Positive sweep mass survives the compact limit. Finite
approximations only need a common measure lower bound; they need not
retain each target value individually. -/
theorem le_volume_projection_iInter_of_compact_antitone
    (ψ : ℝ → Plane → ℝ) (X : Set ℝ) (K : ℕ → Set Plane)
    (hX : IsCompact X) (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ K 0))
    (c : ℝ≥0∞) (hbound : ∀ n, c ≤ volume (scalarProjectionSweep ψ X (K n))) :
    c ≤ volume (scalarProjectionSweep ψ X (⋂ n, K n)) := by
  have hs : ∀ x ∈ X, ContinuousOn (ψ x) (K 0) := by
    intro x hx
    exact hψ.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hq => ⟨hx, hq⟩)
  rw [scalarProjectionSweep_iInter_of_compact_antitone ψ X K hK hanti hs]
  have hc : ∀ n, IsCompact (scalarProjectionSweep ψ X (K n)) := fun n =>
    scalarProjectionSweep_isCompact ψ X (K n) hX (hK n)
      (hψ.mono (prod_mono subset_rfl (hanti (Nat.zero_le n))))
  have ha : Antitone (fun n => scalarProjectionSweep ψ X (K n)) := by
    intro m n hmn p hp
    exact ⟨hp.1, image_mono (hanti hmn) hp.2⟩
  rw [ha.measure_iInter (fun n => (hc n).measurableSet.nullMeasurableSet)
    ⟨0, (hc 0).measure_lt_top.ne⟩]
  exact le_iInf hbound

/-- A sequence of bounds tending to zero proves a zero projection
integral for the actual intersection; no continuity or image
measurability assumption is needed for this monotonicity argument. -/
theorem lintegral_projection_iInter_eq_zero
    (φ : ℝ → Plane → ℝ) (J : Set ℝ) (K : ℕ → Set Plane)
    (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, (∫⁻ t in J, volume (φ t '' K n)) ≤ ε n) :
    (∫⁻ t in J, volume (φ t '' (⋂ n, K n))) = 0 := by
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' hε
  intro n
  exact (lintegral_mono fun t =>
    measure_mono (image_mono (iInter_subset K n))).trans (hbound n)

/-- Construct the compact selection from decreasing compact finite
approximations. Every prescribed centre value survives; the curve
projection integral vanishes. A positive target integral gives a
positive centre projection integral. -/
theorem exists_compact_prescribedProjection_of_nested
    (φ ψ : ℝ → Plane → ℝ) (J X : Set ℝ) (hX : MeasurableSet X)
    (T : ℝ → Set ℝ) (K : ℕ → Set Plane)
    (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    (hψ : ∀ x ∈ X, ContinuousOn (ψ x) (K 0))
    (hretain : ∀ n x, x ∈ X → T x ⊆ ψ x '' K n)
    (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, (∫⁻ t in J, volume (φ t '' K n)) ≤ ε n)
    (hpos : 0 < ∫⁻ x in X, volume (T x)) :
    ∃ G : Set Plane, IsCompact G ∧ MeasurableSet G ∧ G ⊆ K 0 ∧
      (∀ x ∈ X, T x ⊆ ψ x '' G) ∧
      (∫⁻ t in J, volume (φ t '' G)) = 0 ∧
      0 < ∫⁻ x in X, volume (ψ x '' G) := by
  let G := ⋂ n, K n
  have hGc : IsCompact G := isCompact_iInter_of_compact_sequence K hK
  have hGT : ∀ x ∈ X, T x ⊆ ψ x '' G := by
    intro x hx
    rw [continuousOn_image_iInter_of_compact_antitone (ψ x) K hK hanti (hψ x hx)]
    exact subset_iInter fun n => hretain n x hx
  refine ⟨G, hGc, hGc.measurableSet, iInter_subset K 0, hGT,
    lintegral_projection_iInter_eq_zero φ J K ε hε hbound, ?_⟩
  apply hpos.trans_le
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hX] with x hx
  exact measure_mono (hGT x hx)

/-- A positive scalar projection integral entails that the parameter
selection itself is nonempty. -/
theorem nonempty_of_lintegral_scalarProjections_pos
    (ψ : ℝ → Plane → ℝ) (X : Set ℝ) (G : Set Plane)
    (hpos : 0 < ∫⁻ x in X, volume (ψ x '' G)) :
    G.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty.mp h] at hpos
  simp only [image_empty, measure_empty, lintegral_zero, lt_self_iff_false] at hpos

/-- Construct the actual compact null/positive projection selection
from finite approximations with a uniform positive centre mass. Unlike
the target-retention version, no particular projected point must survive
at every finite stage. -/
theorem exists_compact_prescribedProjection_of_nested_mass
    (φ ψ : ℝ → Plane → ℝ) (J X : Set ℝ)
    (K : ℕ → Set Plane) (hX : IsCompact X)
    (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ K 0))
    (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, (∫⁻ t in J, volume (φ t '' K n)) ≤ ε n)
    (c : ℝ≥0∞) (hc : 0 < c)
    (hkeep : ∀ n, c ≤ volume (scalarProjectionSweep ψ X (K n))) :
    ∃ G : Set Plane, IsCompact G ∧ MeasurableSet G ∧ G.Nonempty ∧ G ⊆ K 0 ∧
      (∫⁻ t in J, volume (φ t '' G)) = 0 ∧
      0 < ∫⁻ x in X, volume (ψ x '' G) := by
  let G := ⋂ n, K n
  have hGc : IsCompact G := isCompact_iInter_of_compact_sequence K hK
  have hGs : IsCompact (scalarProjectionSweep ψ X G) :=
    scalarProjectionSweep_isCompact ψ X G hX hGc
      (hψ.mono (prod_mono subset_rfl (iInter_subset K 0)))
  have hGpos : 0 < ∫⁻ x in X, volume (ψ x '' G) := by
    rw [← scalarProjectionSweep_volume_eq_lintegral ψ X G hX.measurableSet
      hGs.measurableSet.nullMeasurableSet]
    exact hc.trans_le
      (le_volume_projection_iInter_of_compact_antitone ψ X K hX hK hanti hψ c hkeep)
  exact ⟨G, hGc, hGc.measurableSet,
    nonempty_of_lintegral_scalarProjections_pos ψ X G hGpos, iInter_subset K 0,
    lintegral_projection_iInter_eq_zero φ J K ε hε hbound, hGpos⟩

/-- Starting with one admissible compact set, recursively perform
finite replacements with errors tending to zero, and construct their
intersection. `P` records the geometric class preserved by the finite
replacement (for example finite unions of closed rectangles).

The replacement hypothesis concerns a single finite stage. It does
not assume an infinite selection or its zero projection property. -/
theorem exists_compact_prescribedProjection_of_refinement
    (φ ψ : ℝ → Plane → ℝ) (J X : Set ℝ) (hX : MeasurableSet X)
    (T : ℝ → Set ℝ) (U K₀ : Set Plane) (P : Set Plane → Prop)
    (hK₀P : P K₀) (hK₀c : IsCompact K₀) (hK₀U : K₀ ⊆ U)
    (hK₀T : ∀ x ∈ X, T x ⊆ ψ x '' K₀)
    (hψ : ∀ x ∈ X, ContinuousOn (ψ x) U)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (hstep : ∀ K, P K → IsCompact K → K ⊆ U →
      (∀ x ∈ X, T x ⊆ ψ x '' K) →
      ∀ δ : ℝ≥0∞, 0 < δ →
        ∃ L : Set Plane, P L ∧ IsCompact L ∧ L ⊆ K ∧
          (∀ x ∈ X, T x ⊆ ψ x '' L) ∧
          (∫⁻ t in J, volume (φ t '' L)) ≤ δ)
    (hpos : 0 < ∫⁻ x in X, volume (T x)) :
    ∃ G : Set Plane, IsCompact G ∧ MeasurableSet G ∧ G ⊆ K₀ ∧
      (∀ x ∈ X, T x ⊆ ψ x '' G) ∧
      (∫⁻ t in J, volume (φ t '' G)) = 0 ∧
      0 < ∫⁻ x in X, volume (ψ x '' G) := by
  classical
  let Good := {K : Set Plane //
    P K ∧ IsCompact K ∧ K ⊆ K₀ ∧ ∀ x ∈ X, T x ⊆ ψ x '' K}
  let initial : Good := ⟨K₀, hK₀P, hK₀c, subset_rfl, hK₀T⟩
  have hnext : ∀ n (K : Good), ∃ L : Good,
      L.val ⊆ K.val ∧ (∫⁻ t in J, volume (φ t '' L.val)) ≤ ε n := by
    intro n K
    obtain ⟨L, hLP, hLc, hLK, hLT, hLb⟩ :=
      hstep K.val K.property.1 K.property.2.1
        (K.property.2.2.1.trans hK₀U) K.property.2.2.2 (ε n) (hεpos n)
    exact ⟨⟨L, hLP, hLc, hLK.trans K.property.2.2.1, hLT⟩, hLK, hLb⟩
  choose next hnextSub hnextBound using hnext
  let S : ℕ → Good :=
    Nat.rec (next 0 initial) (fun n K => next (n + 1) K)
  let K : ℕ → Set Plane := fun n => (S n).val
  have hKc : ∀ n, IsCompact (K n) := fun n => (S n).property.2.1
  have hKU : ∀ n, K n ⊆ K₀ := fun n => (S n).property.2.2.1
  have hKT : ∀ n x, x ∈ X → T x ⊆ ψ x '' K n :=
    fun n => (S n).property.2.2.2
  have hKanti : Antitone K := antitone_nat_of_succ_le fun n =>
    hnextSub (n + 1) (S n)
  have hKb : ∀ n, (∫⁻ t in J, volume (φ t '' K n)) ≤ ε n := by
    intro n
    cases n with
    | zero => exact hnextBound 0 initial
    | succ n => exact hnextBound (n + 1) (S n)
  obtain ⟨G, hGc, hGm, hGK, hGT, hGnull, hGpos⟩ :=
    exists_compact_prescribedProjection_of_nested φ ψ J X hX T K hKc hKanti
      (fun x hx => (hψ x hx).mono ((hKU 0).trans hK₀U))
      hKT ε hε hKb hpos
  exact ⟨G, hGc, hGm, hGK.trans (hKU 0), hGT, hGnull, hGpos⟩

/-- The compact-branch argument for a countable system of compact
pieces. A prescribed value only needs one nested child at each
stage. The whole layers need not be compact or nested. -/
theorem mem_image_limit_of_compact_refinement_system
    (f : Plane → ℝ) (U : Set Plane) (B : ℕ → ℕ → Set Plane)
    (hB : ∀ n i, IsCompact (B n i)) (hBU : ∀ n i, B n i ⊆ U)
    (hf : ContinuousOn f U) (y : ℝ)
    (hstart : y ∈ f '' (⋃ i, B 0 i))
    (hstep : ∀ n i, y ∈ f '' B n i →
      ∃ j, B (n + 1) j ⊆ B n i ∧ y ∈ f '' B (n + 1) j) :
    y ∈ f '' (⋂ n, ⋃ i, B n i) := by
  classical
  obtain ⟨q₀, hq₀, he₀⟩ := hstart
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hq₀
  let Good := fun n => {i : ℕ // y ∈ f '' B n i}
  have hnext : ∀ n (i : Good n), ∃ j : Good (n + 1),
      B (n + 1) j.val ⊆ B n i.val := by
    intro n i
    obtain ⟨j, hsub, hj⟩ := hstep n i.val i.property
    exact ⟨⟨j, hj⟩, hsub⟩
  choose next hnextSub using hnext
  let S : (n : ℕ) → Good n :=
    Nat.rec ⟨i₀, q₀, hi₀, he₀⟩ (fun n i => next n i)
  let K : ℕ → Set Plane := fun n => B n (S n).val
  have hKc : ∀ n, IsCompact (K n) := fun n => hB n (S n).val
  have hKa : Antitone K :=
    antitone_nat_of_succ_le fun n => hnextSub n (S n)
  have hy : y ∈ f '' (⋂ n, K n) := by
    rw [continuousOn_image_iInter_of_compact_antitone f K hKc hKa
      (hf.mono (hBU 0 (S 0).val))]
    exact mem_iInter.mpr fun n => (S n).property
  apply image_mono _ hy
  intro q hq
  exact mem_iInter.mpr fun n =>
    mem_iUnion.mpr ⟨(S n).val, mem_iInter.mp hq n⟩

/-- The countable compact-system version of the selection limit,
corresponding to the compact-branch step in CFMMT Lemma 4.8 on a common
parameter domain. The final Borel set is the actual intersection of
the countable compact layers. The finite replacement and shrinking
projection bounds are explicit hypotheses, not a presumed final set. -/
theorem exists_borel_prescribedProjection_of_compact_system
    (φ ψ : ℝ → Plane → ℝ) (J X : Set ℝ) (hX : MeasurableSet X)
    (T : ℝ → Set ℝ) (U : Set Plane) (B : ℕ → ℕ → Set Plane)
    (hB : ∀ n i, IsCompact (B n i)) (hBU : ∀ n i, B n i ⊆ U)
    (hψ : ∀ x ∈ X, ContinuousOn (ψ x) U)
    (hstart : ∀ x ∈ X, T x ⊆ ψ x '' (⋃ i, B 0 i))
    (hstep : ∀ n i x, x ∈ X → ∀ y ∈ T x, y ∈ ψ x '' B n i →
      ∃ j, B (n + 1) j ⊆ B n i ∧ y ∈ ψ x '' B (n + 1) j)
    (ε : ℕ → ℝ≥0∞) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, (∫⁻ t in J, volume (φ t '' (⋃ i, B n i))) ≤ ε n)
    (hpos : 0 < ∫⁻ x in X, volume (T x)) :
    ∃ G : Set Plane, MeasurableSet G ∧ G.Nonempty ∧ G ⊆ U ∧
      (∀ x ∈ X, T x ⊆ ψ x '' G) ∧
      (∫⁻ t in J, volume (φ t '' G)) = 0 ∧
      0 < ∫⁻ x in X, volume (ψ x '' G) := by
  let G := ⋂ n, ⋃ i, B n i
  have hGm : MeasurableSet G :=
    MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => (hB n i).measurableSet
  have hGU : G ⊆ U := by
    intro q hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp (mem_iInter.mp hq 0)
    exact hBU 0 i hi
  have hGT : ∀ x ∈ X, T x ⊆ ψ x '' G := by
    intro x hx y hy
    exact mem_image_limit_of_compact_refinement_system (ψ x) U B hB hBU (hψ x hx) y
      (hstart x hx hy) (fun n i => hstep n i x hx y hy)
  have hGpos : 0 < ∫⁻ x in X, volume (ψ x '' G) := by
    apply hpos.trans_le
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hX] with x hx
    exact measure_mono (hGT x hx)
  exact ⟨G, hGm, nonempty_of_lintegral_scalarProjections_pos ψ X G hGpos,
    hGU, hGT, lintegral_projection_iInter_eq_zero φ J (fun n => ⋃ i, B n i) ε hε hbound,
    hGpos⟩

end PlanarNikodym
