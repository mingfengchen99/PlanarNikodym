import PlanarNikodym.Projection.CompactProjectionTargetCover

/-! Assembling local finite fans into an interior compact refinement.

The local fan estimate remains an explicit geometric premise. The
finite covering, allocation of error, compact union, interior target
retention, and projection-integral estimate are proved here.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Pointwise

namespace PlanarNikodym

/-- A sign used to orient a centre derivative does not change the
Lebesgue outer measure of any actual scalar projection. -/
theorem volume_signed_scalarProjection {E : Type*}
    (f : E → ℝ) (G : Set E) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    volume ((fun q => σ * f q) '' G) = volume (f '' G) := by
  rcases hσ with rfl | rfl
  · simp
  · simp only [neg_one_mul]
    have he : (fun q => -f q) '' G = -(f '' G) := by
      ext y
      simp only [mem_image, mem_neg]
      constructor
      · rintro ⟨x, hx, h⟩
        exact ⟨x, hx, by linarith⟩
      · rintro ⟨x, hx, h⟩
        exact ⟨x, hx, by linarith⟩
    rw [he, Measure.measure_neg]

/-- Select a positive uniform pointwise tolerance which suffices for
any prescribed positive integral tolerance on a finite-measure window. -/
theorem exists_uniform_scalarProjection_integral_tolerance
    {J : Set ℝ} (hJ : MeasurableSet J) (hJfinite : volume J < ∞)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℝ → ℝ≥0∞,
      (∀ t ∈ J, f t ≤ ENNReal.ofReal ε) → (∫⁻ t in J, f t) ≤ δ := by
  obtain ⟨ε, hε, he⟩ := ENNReal.exists_nnreal_pos_mul_lt hJfinite.ne hδ.ne'
  refine ⟨ε, hε, ?_⟩
  intro f hf
  calc
    (∫⁻ t in J, f t) ≤ ∫⁻ _ in J, ENNReal.ofReal (ε : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hJ] with t ht
      exact hf t ht
    _ = (ε : ℝ≥0∞) * volume J := by simp
    _ ≤ δ := he.le

theorem scalarProjectionSweep_iUnion {ι : Type*}
    (φ : ℝ → Plane → ℝ) (J : Set ℝ) (K : ι → Set Plane) :
    scalarProjectionSweep φ J (⋃ i, K i) =
      ⋃ i, scalarProjectionSweep φ J (K i) := by
  ext p
  simp only [scalarProjectionSweep, mem_setOf_eq, image_iUnion, mem_iUnion]
  constructor
  · rintro ⟨hp, i, hi⟩
    exact ⟨i, hp, hi⟩
  · rintro ⟨i, hp, hi⟩
    exact ⟨hp, i, hi⟩

/-- Subadditivity for actual finite compact parameter pieces. The
section integrals are justified by the completed-measurable sweeps. -/
theorem lintegral_scalarProjections_iUnion_le
    {ι : Type*} [Fintype ι] (φ : ℝ → Plane → ℝ) (J : Set ℝ)
    (hJ : MeasurableSet J) (K : ι → Set Plane)
    (hK : ∀ i, IsCompact (K i))
    (hφ : ∀ i, ContinuousOn (fun p : ℝ × Plane => φ p.1 p.2) (J ×ˢ K i)) :
    (∫⁻ t in J, volume (φ t '' (⋃ i, K i))) ≤
      ∑ i, ∫⁻ t in J, volume (φ t '' K i) := by
  have hmeas (i : ι) : NullMeasurableSet (scalarProjectionSweep φ J (K i)) volume :=
    scalarProjectionSweep_nullMeasurableSet φ J (K i) hJ (hK i).measurableSet (hφ i)
  have hfull : NullMeasurableSet (scalarProjectionSweep φ J (⋃ i, K i)) volume := by
    rw [scalarProjectionSweep_iUnion]
    exact NullMeasurableSet.iUnion hmeas
  rw [← scalarProjectionSweep_volume_eq_lintegral φ J _ hJ hfull,
    scalarProjectionSweep_iUnion]
  calc
    volume (⋃ i, scalarProjectionSweep φ J (K i)) ≤
        ∑ i, volume (scalarProjectionSweep φ J (K i)) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ i, ∫⁻ t in J, volume (φ t '' K i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact scalarProjectionSweep_volume_eq_lintegral φ J (K i) hJ (hmeas i)

/-- A local finite-fan theorem for arbitrarily short transverse
segments suffices to construct one genuine compact refinement of a
fixed interior target. This does not assume a refinement or an
infinite zero-projection selection as a premise. -/
theorem exists_interior_projection_refinement_of_local_fans
    (φ ψ : ℝ → Plane → ℝ) {J X : Set ℝ} {U F K : Set Plane}
    (hJ : MeasurableSet J) (hX : IsOpen X)
    (hKU : K ⊆ U)
    (hF : IsCompact F) (hFK : F ⊆ scalarProjectionSweep ψ X (interior K))
    (hφ : ContinuousOn (fun p : ℝ × Plane => φ p.1 p.2) (J ×ˢ U))
    (hψ : ContinuousOn (fun p : ℝ × Plane => ψ p.1 p.2) (X ×ˢ U))
    (v : Plane)
    (hf : ∀ x ∈ X, ∀ q ∈ U, DifferentiableAt ℝ (ψ x) q)
    (hd : ∀ x ∈ X, ∀ q ∈ U, 0 < fderiv ℝ (ψ x) q v)
    {r : ℝ} (hr : 0 < r)
    (hfan : ∀ W : Set Plane, IsOpen W → W ⊆ U →
      ∀ (c : Plane) (a : ℝ), 0 < a → a < r → centeredBlindSegment c v a ⊆ W →
      ∀ e : ℝ≥0∞, 0 < e →
        ∃ L : Set Plane, IsCompact L ∧ L ⊆ W ∧
          (∀ x ∈ X, ψ x '' centeredBlindSegment c v a ⊆ ψ x '' interior L) ∧
          (∫⁻ t in J, volume (φ t '' L)) ≤ e)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ L : Set Plane, IsCompact L ∧ L ⊆ interior K ∧
      F ⊆ scalarProjectionSweep ψ X (interior L) ∧
      (∫⁻ t in J, volume (φ t '' L)) ≤ δ := by
  classical
  have hIU : interior K ⊆ U := interior_subset.trans hKU
  obtain ⟨C, hC, hcover⟩ := exists_finite_transverseSegment_cover
    ψ hX isOpen_interior hF hFK (hψ.mono (prod_mono subset_rfl hIU)) v
    (fun x hx q hq => hf x hx q (hIU hq))
    (fun x hx q hq => hd x hx q (hIU hq)) hr
  let I := ↥C
  let e : ℝ≥0∞ := δ / ((Fintype.card I : ℝ≥0∞) + 1)
  have he : 0 < e := ENNReal.div_pos hδ.ne' (by simp)
  have hex (p : I) :
      ∃ L : Set Plane, IsCompact L ∧ L ⊆ interior K ∧
        (∀ x ∈ X, ψ x '' centeredBlindSegment p.val.1 v p.val.2 ⊆ ψ x '' interior L) ∧
        (∫⁻ t in J, volume (φ t '' L)) ≤ e :=
    hfan (interior K) isOpen_interior hIU p.val.1 p.val.2
      (hC p.val p.property).1 (hC p.val p.property).2.1 (hC p.val p.property).2.2 e he
  choose L hLc hLK hretain hsmall using hex
  let G : Set Plane := ⋃ p : I, L p
  have hLG (p : I) : L p ⊆ G := subset_iUnion L p
  refine ⟨G, isCompact_iUnion hLc, iUnion_subset hLK, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp (hcover hz)
    have hzs := interior_subset hzp
    refine ⟨hzs.1, ?_⟩
    exact image_mono (interior_mono (hLG ⟨p, hp⟩))
      (hretain ⟨p, hp⟩ z.1 hzs.1 hzs.2)
  · calc
      (∫⁻ t in J, volume (φ t '' G)) ≤ ∑ p : I, ∫⁻ t in J, volume (φ t '' L p) :=
        lintegral_scalarProjections_iUnion_le φ J hJ L hLc
          (fun p => hφ.mono (prod_mono subset_rfl ((hLK p).trans hIU)))
      _ ≤ ∑ _p : I, e := Finset.sum_le_sum (fun p _ => hsmall p)
      _ = (Fintype.card I : ℝ≥0∞) * e := by simp
      _ ≤ ((Fintype.card I : ℝ≥0∞) + 1) * e :=
        mul_le_mul_left (le_add_right le_rfl) e
      _ = δ := by
        dsimp [e]
        rw [mul_comm, ENNReal.div_mul_cancel] <;> simp

end PlanarNikodym
