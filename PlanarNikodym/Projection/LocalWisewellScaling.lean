import PlanarNikodym.Projection.FactorialNullSweep
import PlanarNikodym.Projection.WisewellLocalGeometry

/-! Actual local scaling for the bounded Wisewell construction.

The cancellation slope is bounded on a compact regular box before the
parameter scale is chosen.  Only the parameter coordinates are changed:
the resulting compact null sweep already lies in the original plane. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym.Wisewell

/-- A common scaling of both parameters multiplies each parameter
derivative by the same scalar. -/
theorem fderiv_affine_parameter_slice (f : ℝ × Plane → ℝ)
    (t : ℝ) (q₀ q : Plane) (δ : ℝ)
    (hf : DifferentiableAt ℝ f (t, q₀ + δ • q)) (v : Plane) :
    fderiv ℝ (fun p : Plane => f (t, q₀ + δ • p)) q v =
      δ * fderiv ℝ f (t, q₀ + δ • q) (0, v) := by
  have hi : HasFDerivAt (fun p : Plane => (t, q₀ + δ • p))
      ((0 : Plane →L[ℝ] ℝ).prod (δ • ContinuousLinearMap.id ℝ Plane)) q :=
    (hasFDerivAt_const t q).prodMk
      ((hasFDerivAt_id q).const_smul δ |>.const_add q₀)
  change fderiv ℝ (f ∘ fun p : Plane => (t, q₀ + δ • p)) q v = _
  rw [(hf.hasFDerivAt.comp q hi).fderiv]
  change fderiv ℝ f (t, q₀ + δ • q) (0, δ • v) = _
  rw [show ((0, δ • v) : ℝ × Plane) = δ • (0, v) by simp, map_smul]
  rfl

/-- At a point with nonzero second parameter derivative, an analytic
scalar family has a compact null set containing a selected curve for
every parameter in a genuine interval of positive length.  The selected
second parameter stays in the original regular box. -/
theorem exists_compact_null_curves_on_regular_box
    (f : ℝ × Plane → ℝ) (t₀ : ℝ) (q₀ : Plane) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℝ f (closedBall (t₀, q₀) r))
    (hβ : ∀ p ∈ closedBall (t₀, q₀) r, scalarTailDerivative f p ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r ∧ ∃ E : Set Plane,
      IsCompact E ∧ volume E = 0 ∧
      ∀ y ∈ Icc q₀.1 (q₀.1 + δ), ∃ s ∈ ball q₀.2 r,
        (fun t => (t, f (t, (y, s)))) '' closedBall t₀ (r / 2) ⊆ E := by
  let slope : ℝ × Plane → ℝ := fun p => scalarHeadDerivative f p / scalarTailDerivative f p
  have hslope : ContinuousOn slope (closedBall (t₀, q₀) r) := by
    intro p hp
    exact (((scalarHeadDerivative_analyticAt (hf p hp)).div
      (scalarTailDerivative_analyticAt (hf p hp)) (hβ p hp)).continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (t₀, q₀) r).exists_bound_of_continuousOn hslope
  let M : ℝ := max 1 B + 1
  have hM : 0 < M := by dsimp [M]; have := le_max_left (1 : ℝ) B; linarith
  have hM1 : 1 < M := by dsimp [M]; have := le_max_left (1 : ℝ) B; linarith
  let δ : ℝ := r / (2 * (M + 1))
  have hδ : 0 < δ := div_pos hr (by positivity)
  have hδr : δ < r := by
    dsimp [δ]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (M + 1))).mpr
    nlinarith
  have hδMr : δ * M < r := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (M + 1))).mpr
    nlinarith
  let K : Set ℝ := closedBall t₀ (r / 2)
  let R : Set Plane := Icc (0 : ℝ) 1 ×ˢ Icc (-M) M
  let F : ℝ × Plane → ℝ := fun p => f (p.1, q₀ + δ • p.2)
  have hQ (q : Plane) (hq : q ∈ R) : q₀ + δ • q ∈ closedBall q₀ r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Prod.norm_def]
    apply max_le
    · change ‖δ * q.1‖ ≤ r
      rw [norm_mul, Real.norm_of_nonneg hδ.le, Real.norm_of_nonneg hq.1.1]
      exact (mul_le_of_le_one_right hδ.le hq.1.2).trans hδr.le
    · change ‖δ * q.2‖ ≤ r
      rw [norm_mul, Real.norm_of_nonneg hδ.le, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr hq.2) hδ.le).trans hδMr.le
  have hdom (p : ℝ × Plane) (hp : p ∈ K ×ˢ R) :
      (p.1, q₀ + δ • p.2) ∈ closedBall (t₀, q₀) r := by
    rw [← closedBall_prod_same]
    exact ⟨closedBall_subset_closedBall (by linarith) hp.1, hQ p.2 hp.2⟩
  have hF (p : ℝ × Plane) (hp : p ∈ K ×ˢ R) : AnalyticAt ℝ F p := by
    exact (hf _ (hdom p hp)).comp (f := fun p : ℝ × Plane => (p.1, q₀ + δ • p.2))
      (analyticAt_fst.prod (analyticAt_const.add (analyticAt_snd.const_smul (c := δ))))
  have hFslice (t : ℝ) (ht : t ∈ K) (q : Plane) (hq : q ∈ R) :
      AnalyticAt ℝ (fun p : Plane => F (t, p)) q :=
    (hF (t, q) ⟨ht, hq⟩).comp (f := fun p : Plane => (t, p))
      (analyticAt_const.prod analyticAt_id)
  have hderiv (t : ℝ) (ht : t ∈ K) (q : Plane) (hq : q ∈ R) (v : Plane) :
      fderiv ℝ (fun p : Plane => F (t, p)) q v =
        δ * fderiv ℝ f (t, q₀ + δ • q) (0, v) :=
    fderiv_affine_parameter_slice f t q₀ q δ (hf _ (hdom (t, q) ⟨ht, hq⟩)).differentiableAt v
  obtain ⟨ψ, E, _, hψ, hEc, hE0, hE⟩ :=
    exists_compact_null_curves_of_bounded_slope M hM.le F K (isCompact_closedBall _ _)
      (fun p hp => (hF p hp).continuousAt.continuousWithinAt)
      (fun t ht q hq => (hFslice t ht q hq).differentiableAt)
      (fun t ht q hq => (hFslice t ht q hq).fderiv.continuousAt.continuousWithinAt)
      (fun t ht q hq => by
        rw [hderiv t ht q hq (0, 1)]
        exact mul_ne_zero hδ.ne' (hβ _ (hdom (t, q) ⟨ht, hq⟩)))
      (fun t ht q hq => by
        rw [hderiv t ht q hq (1, 0), hderiv t ht q hq (0, 1),
          mul_div_mul_left _ _ hδ.ne']
        have hbound := hB (t, q₀ + δ • q) (hdom (t, q) ⟨ht, hq⟩)
        change |slope (t, q₀ + δ • q)| < M
        rw [← Real.norm_eq_abs]
        exact hbound.trans_lt (by dsimp [M]; have := le_max_right (1 : ℝ) B; linarith))
  refine ⟨δ, hδ, hδr, E, hEc, hE0, ?_⟩
  intro y hy
  let u : ℝ := (y - q₀.1) / δ
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy.1) hδ.le
    · exact (div_le_one hδ).mpr (by linarith [hy.2])
  refine ⟨q₀.2 + δ * ψ u, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Real.norm_of_nonneg hδ.le]
    exact (mul_le_mul_of_nonneg_left (hψ u) hδ.le).trans_lt hδMr
  · rintro _ ⟨t, ht, rfl⟩
    have heq : q₀ + δ • (u, ψ u) = (y, q₀.2 + δ * ψ u) := by
      ext
      · change q₀.1 + δ * ((y - q₀.1) / δ) = y
        field_simp; ring
      · rfl
    have hmem := hE u hu (Set.mem_image_of_mem (fun t => (t, F (t, (u, ψ u)))) ht)
    simpa only [F, heq] using hmem

end PlanarNikodym.Wisewell
