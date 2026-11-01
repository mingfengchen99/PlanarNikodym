import PlanarNikodym.Projection.NonlinearBlindReplacement
import PlanarNikodym.Projection.ProjectedSweepTransfer
import PlanarNikodym.Projection.PrescribedProjectionLimit

/-! Finite transverse-segment covers of compact projection targets.

Every point of a projected open parameter set is an interior point of
the sweep of a sufficiently short transverse segment. Compactness then
selects finitely many such segments, all contained in the original open
set. This is the target-cover step needed before finite blind
replacement and compact refinement.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PlanarNikodym

/-- A transverse segment can be chosen inside an open parameter set
with any prescribed positive upper bound on its half-length. -/
theorem exists_small_centeredBlindSegment_subset
    {U : Set Plane} (hU : IsOpen U) {c : Plane} (hc : c ∈ U)
    (v : Plane) {η : ℝ} (hη : 0 < η) :
    ∃ a : ℝ, 0 < a ∧ a < η ∧ centeredBlindSegment c v a ⊆ U := by
  have hcont : Continuous (fun t : ℝ => c + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun t : ℝ => c + t • v) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hc)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let a := min r η / 2
  have ha : 0 < a := half_pos (lt_min hr hη)
  have har : a < r := (half_lt_self (lt_min hr hη)).trans_le (min_le_left _ _)
  have haη : a < η := (half_lt_self (lt_min hr hη)).trans_le (min_le_right _ _)
  refine ⟨a, ha, haη, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  apply hball
  rw [mem_ball, Real.dist_eq, sub_zero]
  exact (abs_le.mpr ht).trans_lt har

/-- The open strip strictly between the projected segment endpoints. -/
def blindProjectionStrip
    (ψ : ℝ → Plane → ℝ) (X : Set ℝ) (c v : Plane) (a : ℝ) : Set Plane :=
  {p | p.1 ∈ X ∧ ψ p.1 (c + (-a) • v) < p.2 ∧
    p.2 < ψ p.1 (c + a • v)}

theorem blindProjectionStrip_isOpen
    (ψ : ℝ → Plane → ℝ) {X : Set ℝ} {U : Set Plane}
    (hX : IsOpen X) (hU : IsOpen U)
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ U))
    {c v : Plane} {a : ℝ}
    (hlo : c + (-a) • v ∈ U) (hhi : c + a • v ∈ U) :
    IsOpen (blindProjectionStrip ψ X c v a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hl : ContinuousAt (fun z : Plane => ψ z.1 (c + (-a) • v)) p :=
    (hψ.continuousAt ((hX.prod hU).mem_nhds ⟨hp.1, hlo⟩)).comp
      (continuousAt_fst.prodMk continuousAt_const)
  have hu : ContinuousAt (fun z : Plane => ψ z.1 (c + a • v)) p :=
    (hψ.continuousAt ((hX.prod hU).mem_nhds ⟨hp.1, hhi⟩)).comp
      (continuousAt_fst.prodMk continuousAt_const)
  have hx : ∀ᶠ z : Plane in 𝓝 p, z.1 ∈ X :=
    continuousAt_fst.preimage_mem_nhds (hX.mem_nhds hp.1)
  have hlow : ∀ᶠ z : Plane in 𝓝 p, 0 < z.2 - ψ z.1 (c + (-a) • v) :=
    (continuousAt_snd.sub hl).preimage_mem_nhds (isOpen_Ioi.mem_nhds (sub_pos.mpr hp.2.1))
  have hupp : ∀ᶠ z : Plane in 𝓝 p, 0 < ψ z.1 (c + a • v) - z.2 :=
    (hu.sub continuousAt_snd).preimage_mem_nhds (isOpen_Ioi.mem_nhds (sub_pos.mpr hp.2.2))
  filter_upwards [hx, hlow, hupp] with z hz hlz huz
  exact ⟨hz, sub_pos.mp hlz, sub_pos.mp huz⟩

/-- The intermediate value theorem puts the whole endpoint strip in
the actual sweep of the segment. -/
theorem blindProjectionStrip_subset_sweep
    (ψ : ℝ → Plane → ℝ) {X : Set ℝ} {U : Set Plane}
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ U))
    {c v : Plane} {a : ℝ} (ha : 0 ≤ a)
    (hseg : centeredBlindSegment c v a ⊆ U) :
    blindProjectionStrip ψ X c v a ⊆
      scalarProjectionSweep ψ X (centeredBlindSegment c v a) := by
  intro p hp
  have hcont : ContinuousOn (fun t : ℝ => ψ p.1 (c + t • v)) (Icc (-a) a) :=
    hψ.comp
      (continuousOn_const.prodMk
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
      (fun t ht => ⟨hp.1, hseg ⟨t, ht, rfl⟩⟩)
  obtain ⟨t, ht, he⟩ :=
    intermediate_value_Icc (by linarith : -a ≤ a) hcont ⟨hp.2.1.le, hp.2.2.le⟩
  exact ⟨hp.1, c + t • v, ⟨t, ht, rfl⟩, he⟩

/-- A positive directional derivative gives strict monotonicity along
each actual parameter segment. -/
theorem strictMonoOn_blindSegment_projection
    {f : Plane → ℝ} {U : Set Plane} {c v : Plane} {a : ℝ}
    (hf : ∀ q ∈ U, DifferentiableAt ℝ f q)
    (hd : ∀ q ∈ U, 0 < fderiv ℝ f q v)
    (hseg : centeredBlindSegment c v a ⊆ U) :
    StrictMonoOn (fun t : ℝ => f (c + t • v)) (Icc (-a) a) := by
  have hg : ∀ t ∈ Icc (-a) a,
      HasDerivAt (fun t : ℝ => f (c + t • v)) (fderiv ℝ f (c + t • v) v) t := by
    intro t ht
    exact (hf _ (hseg ⟨t, ht, rfl⟩)).hasFDerivAt.comp_hasDerivAt t
      (by simpa using ((hasDerivAt_id t).smul_const v).const_add c)
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
  intro t ht
  rw [(hg t (interior_subset ht)).deriv]
  exact hd _ (hseg ⟨t, interior_subset ht, rfl⟩)

/-- The central projected point belongs to the interior of the segment
sweep. This supplies an actual open neighbourhood for compact covering. -/
theorem mem_interior_sweep_centeredBlindSegment
    (ψ : ℝ → Plane → ℝ) {X : Set ℝ} {U : Set Plane}
    (hX : IsOpen X) (hU : IsOpen U)
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ U))
    {x : ℝ} (hx : x ∈ X) {c v : Plane} {a : ℝ} (ha : 0 < a)
    (hf : ∀ q ∈ U, DifferentiableAt ℝ (ψ x) q)
    (hd : ∀ q ∈ U, 0 < fderiv ℝ (ψ x) q v)
    (hseg : centeredBlindSegment c v a ⊆ U) :
    (x, ψ x c) ∈ interior (scalarProjectionSweep ψ X (centeredBlindSegment c v a)) := by
  have hlo : c + (-a) • v ∈ U := hseg ⟨-a, ⟨le_rfl, by linarith⟩, rfl⟩
  have hhi : c + a • v ∈ U := hseg ⟨a, ⟨by linarith, le_rfl⟩, rfl⟩
  have hmono := strictMonoOn_blindSegment_projection hf hd hseg
  have hbelow : ψ x (c + (-a) • v) < ψ x c := by
    simpa using hmono (show -a ∈ Icc (-a) a from ⟨le_rfl, by linarith⟩)
      (show 0 ∈ Icc (-a) a from ⟨by linarith, ha.le⟩) (by linarith : -a < 0)
  have habove : ψ x c < ψ x (c + a • v) := by
    simpa using hmono (show 0 ∈ Icc (-a) a from ⟨by linarith, ha.le⟩)
      (show a ∈ Icc (-a) a from ⟨by linarith, le_rfl⟩) ha
  exact interior_maximal (blindProjectionStrip_subset_sweep ψ hψ ha.le hseg)
    (blindProjectionStrip_isOpen ψ hX hU hψ hlo hhi) ⟨hx, hbelow, habove⟩

/-- A compact target in the sweep of an open parameter set is covered
by the interiors of finitely many actual transverse segment sweeps.
All segments stay inside the open set and can be required arbitrarily
short. No finite cover or open projected image is supplied as an input. -/
theorem exists_finite_transverseSegment_cover
    (ψ : ℝ → Plane → ℝ) {X : Set ℝ} {U F : Set Plane}
    (hX : IsOpen X) (hU : IsOpen U) (hF : IsCompact F)
    (hFU : F ⊆ scalarProjectionSweep ψ X U)
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ U))
    (v : Plane)
    (hf : ∀ x ∈ X, ∀ q ∈ U, DifferentiableAt ℝ (ψ x) q)
    (hd : ∀ x ∈ X, ∀ q ∈ U, 0 < fderiv ℝ (ψ x) q v)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : Finset (Plane × ℝ),
      (∀ p ∈ C, 0 < p.2 ∧ p.2 < η ∧ centeredBlindSegment p.1 v p.2 ⊆ U) ∧
      F ⊆ ⋃ p ∈ C, interior (scalarProjectionSweep ψ X (centeredBlindSegment p.1 v p.2)) := by
  classical
  let Good := {p : Plane × ℝ //
    0 < p.2 ∧ p.2 < η ∧ centeredBlindSegment p.1 v p.2 ⊆ U}
  let O : Good → Set Plane := fun p =>
    interior (scalarProjectionSweep ψ X (centeredBlindSegment p.val.1 v p.val.2))
  have hcover : F ⊆ ⋃ p : Good, O p := by
    intro y hy
    obtain ⟨hyX, c, hc, he⟩ := hFU hy
    obtain ⟨a, ha, haη, hseg⟩ := exists_small_centeredBlindSegment_subset hU hc v hη
    let p : Good := ⟨(c, a), ha, haη, hseg⟩
    apply mem_iUnion.mpr
    refine ⟨p, ?_⟩
    have hm := mem_interior_sweep_centeredBlindSegment ψ hX hU hψ hyX ha
      (hf y.1 hyX) (hd y.1 hyX) hseg
    simpa only [O, p, he, Prod.eta] using hm
  obtain ⟨C, hC⟩ := hF.elim_finite_subcover O (fun _ => isOpen_interior) hcover
  refine ⟨C.image Subtype.val, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  · intro y hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion.mp (hC hy) |>.imp fun p => mem_iUnion.mp
    exact mem_iUnion.mpr ⟨p.val, mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, hyp⟩⟩

/-- Construct a compact initial parameter set and a genuinely positive
compact target lying in the sweep of its interior. This strict interior
invariant allows later finite replacements to shrink the parameter set. -/
theorem exists_compact_positive_interior_projection_target
    (ψ : ℝ → Plane → ℝ) {X : Set ℝ} {U : Set Plane}
    (hX : IsOpen X) (hU : IsOpen U) (hXn : X.Nonempty) (hUn : U.Nonempty)
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ U))
    (v : Plane)
    (hf : ∀ x ∈ X, ∀ q ∈ U, DifferentiableAt ℝ (ψ x) q)
    (hd : ∀ x ∈ X, ∀ q ∈ U, 0 < fderiv ℝ (ψ x) q v) :
    ∃ K F : Set Plane, IsCompact K ∧ K ⊆ U ∧ IsCompact F ∧ 0 < volume F ∧
      F ⊆ scalarProjectionSweep ψ X (interior K) := by
  obtain ⟨x, hx⟩ := hXn
  obtain ⟨c, hc⟩ := hUn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  let K : Set Plane := closedBall c (r / 2)
  have hKU : K ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hcK : c ∈ interior K :=
    interior_maximal ball_subset_closedBall isOpen_ball (mem_ball_self (half_pos hr))
  obtain ⟨a, ha, _, hseg⟩ :=
    exists_small_centeredBlindSegment_subset isOpen_interior hcK v (show 0 < (1 : ℝ) by norm_num)
  have hI : interior K ⊆ U := interior_subset.trans hKU
  have hm := mem_interior_sweep_centeredBlindSegment ψ hX isOpen_interior
    (hψ.mono (prod_mono subset_rfl hI)) hx ha
    (fun q hq => hf x hx q (hI hq)) (fun q hq => hd x hx q (hI hq)) hseg
  obtain ⟨ρ, hρ, hρsub⟩ :=
    Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hm)
  let F : Set Plane := closedBall (x, ψ x c) (ρ / 2)
  have hFs : F ⊆ scalarProjectionSweep ψ X (centeredBlindSegment c v a) :=
    ((closedBall_subset_ball (half_lt_self hρ)).trans hρsub).trans interior_subset
  refine ⟨K, F, isCompact_closedBall _ _, hKU, isCompact_closedBall _ _,
    Metric.measure_closedBall_pos volume _ (half_pos hρ), ?_⟩
  intro y hy
  obtain ⟨hyX, q, hq, he⟩ := hFs hy
  exact ⟨hyX, q, hseg hq, he⟩

/-- The section targets of a Borel planar target have precisely its
planar measure as their projection integral. -/
theorem lintegral_compactTarget_sections_eq_volume
    {X : Set ℝ} {F : Set Plane} (hX : MeasurableSet X)
    (hF : MeasurableSet F) (hFX : ∀ p ∈ F, p.1 ∈ X) :
    (∫⁻ x in X, volume (Prod.mk x ⁻¹' F)) = volume F := by
  change (∫⁻ x in X, volume (Prod.mk x ⁻¹' F)) = (volume.prod volume) F
  rw [Measure.prod_apply hF, ← lintegral_indicator hX]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ X
  · simp only [indicator_of_mem hx]
  · have he : Prod.mk x ⁻¹' F = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hx (hFX (x, y) hy)
    simp only [indicator_of_notMem hx, he, measure_empty]

/-- The compact interior-invariant route to a prescribed-projection
selection. The positive target integral is proved from the actual
compact target by Fubini. The remaining geometric hypothesis is the
single finite replacement inside `interior K`; it must still be proved
by the iterated blind construction and its controlled thickening. -/
theorem exists_compact_prescribedProjection_of_interior_refinement
    (φ ψ : ℝ → Plane → ℝ) (J X : Set ℝ) (hX : MeasurableSet X)
    (U K₀ F : Set Plane) (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ U)
    (hF : IsCompact F) (hFpos : 0 < volume F)
    (hinit : F ⊆ scalarProjectionSweep ψ X (interior K₀))
    (hψ : ∀ x ∈ X, ContinuousOn (ψ x) U)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (hstep : ∀ K : Set Plane, IsCompact K → K ⊆ U →
      F ⊆ scalarProjectionSweep ψ X (interior K) →
      ∀ δ : ℝ≥0∞, 0 < δ →
        ∃ L : Set Plane, IsCompact L ∧ L ⊆ interior K ∧
          F ⊆ scalarProjectionSweep ψ X (interior L) ∧
          (∫⁻ t in J, volume (φ t '' L)) ≤ δ) :
    ∃ G : Set Plane, IsCompact G ∧ MeasurableSet G ∧ G.Nonempty ∧ G ⊆ K₀ ∧
      F ⊆ scalarProjectionSweep ψ X G ∧
      (∫⁻ t in J, volume (φ t '' G)) = 0 ∧
      0 < ∫⁻ x in X, volume (ψ x '' G) := by
  let T : ℝ → Set ℝ := fun x => Prod.mk x ⁻¹' F
  let P : Set Plane → Prop := fun K => F ⊆ scalarProjectionSweep ψ X (interior K)
  have hFX : ∀ p ∈ F, p.1 ∈ X := fun p hp => (hinit hp).1
  have hTpos : 0 < ∫⁻ x in X, volume (T x) := by
    change 0 < ∫⁻ x in X, volume (Prod.mk x ⁻¹' F)
    rw [lintegral_compactTarget_sections_eq_volume hX hF.measurableSet hFX]
    exact hFpos
  have hretain : ∀ K, P K → ∀ x ∈ X, T x ⊆ ψ x '' K := by
    intro K hP x hx y hy
    exact image_mono interior_subset (hP hy).2
  obtain ⟨G, hGc, hGm, hGK, hGT, hGnull, hGpos⟩ :=
    exists_compact_prescribedProjection_of_refinement φ ψ J X hX T U K₀ P
      hinit hK₀ hK₀U (hretain K₀ hinit) hψ ε hεpos hε
      (fun K hP hKc hKU _ δ hδ => by
        obtain ⟨L, hLc, hLK, hLF, hLb⟩ := hstep K hKc hKU hP δ hδ
        exact ⟨L, hLF, hLc, hLK.trans interior_subset, hretain L hLF, hLb⟩)
      hTpos
  refine ⟨G, hGc, hGm, nonempty_of_lintegral_scalarProjections_pos ψ X G hGpos,
    hGK, ?_, hGnull, hGpos⟩
  intro p hp
  exact ⟨hFX p hp, hGT p.1 (hFX p hp) hp⟩

end PlanarNikodym
