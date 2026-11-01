import PlanarNikodym.Projection.WisewellLocalGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Local geometry for the nonstationary branch of §7.3.

These results construct genuine compact product neighbourhoods with a
nonzero parameter gradient and a uniformly oriented, strictly monotone
projective slope. They do not assume a prescribed-projection selection
set, and do not construct that set.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace PlanarNikodym

theorem scalarGradientSlope_deriv_eq_timeDerivative
    {ψ : ℝ × Plane → ℝ} {p : ℝ × Plane}
    (hψ : AnalyticAt ℝ ψ p) (hh : scalarHeadDerivative ψ p ≠ 0) :
    deriv (fun t => scalarGradientSlope ψ (t, p.2)) p.1 =
      timeDerivative (scalarGradientSlope ψ) 1 p := by
  simpa only [iteratedDeriv_one] using
    (timeDerivative_eq_iteratedDeriv 1 p (scalarGradientSlope_analyticAt hψ hh)).symm

/-- A nonzero derivative rules out constancy on every neighbourhood,
including constancy at an arbitrarily prescribed slope. -/
theorem exists_mem_ne_of_deriv_ne_zero {f : ℝ → ℝ} {t : ℝ} {U : Set ℝ}
    (hU : U ∈ 𝓝 t) (hd : deriv f t ≠ 0) (c : ℝ) :
    ∃ s ∈ U, f s ≠ c := by
  by_contra! h
  have he : f =ᶠ[𝓝 t] fun _ => c := by
    filter_upwards [hU] with s hs
    exact h s hs
  exact hd (he.deriv_eq.trans (deriv_const t c))

/-- Nonstationarity at a regular point gives an actual closed product
box on which all parameter slices have the same strict orientation.
The sign is shared by every slice; the derivative stays nonzero up to
the boundary of the box. -/
theorem exists_scalarGradientSlope_monotone_patch
    {ψ : ℝ × Plane → ℝ} {U : Set (ℝ × Plane)} (hU : IsOpen U)
    {p : ℝ × Plane} (hp : p ∈ U) (hψ : AnalyticAt ℝ ψ p)
    (hh : scalarHeadDerivative ψ p ≠ 0)
    (hd : deriv (fun t => scalarGradientSlope ψ (t, p.2)) p.1 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      closedBall p r ⊆ U ∧
      (∀ z ∈ closedBall p r, AnalyticAt ℝ ψ z ∧
        scalarHeadDerivative ψ z ≠ 0 ∧
        0 < σ * deriv (fun t => scalarGradientSlope ψ (t, z.2)) z.1) ∧
      ∀ q ∈ closedBall p.2 r,
        StrictMonoOn (fun t => σ * scalarGradientSlope ψ (t, q)) (closedBall p.1 r) := by
  let δ := timeDerivative (scalarGradientSlope ψ) 1
  have hδa : AnalyticAt ℝ δ p :=
    timeDerivative_analyticAt (scalarGradientSlope_analyticAt hψ hh) 1
  have hδ : δ p ≠ 0 := by
    rwa [scalarGradientSlope_deriv_eq_timeDerivative hψ hh] at hd
  obtain ⟨σ, hσ, hσδ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * δ p := by
    rcases lt_or_gt_of_ne hδ with hn | hp
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by simpa using hp⟩
  have hsign : ∀ᶠ z in 𝓝 p, 0 < σ * δ z :=
    (continuousAt_const.mul hδa.continuousAt).preimage_mem_nhds
      (isOpen_Ioi.mem_nhds hσδ)
  have hgood : ∀ᶠ z in 𝓝 p, z ∈ U ∧ AnalyticAt ℝ ψ z ∧
      scalarHeadDerivative ψ z ≠ 0 ∧ 0 < σ * δ z := by
    filter_upwards [hU.mem_nhds hp, hψ.eventually_analyticAt,
      (scalarHeadDerivative_analyticAt hψ).continuousAt.eventually_ne hh, hsign]
      with z hz ha hhead hs
    exact ⟨hz, ha, hhead, hs⟩
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let r := a / 2
  have hr : 0 < r := half_pos ha
  have hbox (z : ℝ × Plane) (hz : z ∈ closedBall p r) :
      z ∈ U ∧ AnalyticAt ℝ ψ z ∧ scalarHeadDerivative ψ z ≠ 0 ∧
        0 < σ * deriv (fun t => scalarGradientSlope ψ (t, z.2)) z.1 := by
    obtain ⟨hdom, han, hhead, hs⟩ := hball (closedBall_subset_ball (half_lt_self ha) hz)
    exact ⟨hdom, han, hhead, by
      rwa [scalarGradientSlope_deriv_eq_timeDerivative han hhead]⟩
  refine ⟨r, hr, σ, hσ, fun z hz => (hbox z hz).1,
    fun z hz => (hbox z hz).2, ?_⟩
  intro q hq
  have hpair (t : ℝ) (ht : t ∈ closedBall p.1 r) : (t, q) ∈ closedBall p r := by
    rw [← closedBall_prod_same]
    exact ⟨ht, hq⟩
  have han (t : ℝ) (ht : t ∈ closedBall p.1 r) :
      AnalyticAt ℝ (fun t => scalarGradientSlope ψ (t, q)) t :=
    (scalarGradientSlope_analyticAt (hbox (t, q) (hpair t ht)).2.1
      (hbox (t, q) (hpair t ht)).2.2.1).comp
        (f := fun t : ℝ => (t, q)) (analyticAt_id.prod analyticAt_const)
  apply strictMonoOn_of_deriv_pos (convex_closedBall _ _)
    (fun t ht => ((analyticAt_const.mul (han t ht)).continuousAt.continuousWithinAt))
  intro t ht
  change 0 < deriv (fun t => σ * scalarGradientSlope ψ (t, q)) t
  rw [deriv_const_mul_field]
  exact (hbox (t, q) (hpair t (interior_subset ht))).2.2.2

/-- Two distinct rotating directions admit a common parameter radius,
uniform strict orientations, and disjoint slope ranges on the entire
closed boxes. This is the local separation needed before applying the
nonlinear prescribed-projection construction. -/
theorem exists_separated_scalarGradientSlope_patches
    {φ ψ : ℝ × Plane → ℝ} {U V : Set (ℝ × Plane)}
    (hU : IsOpen U) (hV : IsOpen V) (t x : ℝ) (q : Plane)
    (htq : (t, q) ∈ U) (hxq : (x, q) ∈ V)
    (hφ : AnalyticAt ℝ φ (t, q)) (hψ : AnalyticAt ℝ ψ (x, q))
    (hhφ : scalarHeadDerivative φ (t, q) ≠ 0)
    (hhψ : scalarHeadDerivative ψ (x, q) ≠ 0)
    (hdφ : deriv (fun s => scalarGradientSlope φ (s, q)) t ≠ 0)
    (hdψ : deriv (fun s => scalarGradientSlope ψ (s, q)) x ≠ 0)
    (hne : scalarGradientSlope φ (t, q) ≠ scalarGradientSlope ψ (x, q)) :
    ∃ r : ℝ, 0 < r ∧ ∃ σφ σψ : ℝ,
      (σφ = 1 ∨ σφ = -1) ∧ (σψ = 1 ∨ σψ = -1) ∧
      closedBall (t, q) r ⊆ U ∧ closedBall (x, q) r ⊆ V ∧
      (∀ z ∈ closedBall (t, q) r, AnalyticAt ℝ φ z ∧
        scalarHeadDerivative φ z ≠ 0 ∧
        0 < σφ * deriv (fun s => scalarGradientSlope φ (s, z.2)) z.1) ∧
      (∀ z ∈ closedBall (x, q) r, AnalyticAt ℝ ψ z ∧
        scalarHeadDerivative ψ z ≠ 0 ∧
        0 < σψ * deriv (fun s => scalarGradientSlope ψ (s, z.2)) z.1) ∧
      (∀ v ∈ closedBall q r,
        StrictMonoOn (fun s => σφ * scalarGradientSlope φ (s, v)) (closedBall t r) ∧
        StrictMonoOn (fun s => σψ * scalarGradientSlope ψ (s, v)) (closedBall x r)) ∧
      ∀ z ∈ closedBall (t, q) r, ∀ w ∈ closedBall (x, q) r,
        scalarGradientSlope φ z ≠ scalarGradientSlope ψ w := by
  obtain ⟨a, ha, σφ, hσφ, hUa, hφa, hmφ⟩ :=
    exists_scalarGradientSlope_monotone_patch hU htq hφ hhφ hdφ
  obtain ⟨b, hb, σψ, hσψ, hVb, hψb, hmψ⟩ :=
    exists_scalarGradientSlope_monotone_patch hV hxq hψ hhψ hdψ
  have hcφ : ContinuousAt (fun z : (ℝ × Plane) × (ℝ × Plane) =>
      scalarGradientSlope φ z.1) ((t, q), (x, q)) :=
    (scalarGradientSlope_analyticAt hφ hhφ).continuousAt.comp
      (f := fun z : (ℝ × Plane) × (ℝ × Plane) => z.1)
      (x := ((t, q), (x, q))) continuousAt_fst
  have hcψ : ContinuousAt (fun z : (ℝ × Plane) × (ℝ × Plane) =>
      scalarGradientSlope ψ z.2) ((t, q), (x, q)) :=
    (scalarGradientSlope_analyticAt hψ hhψ).continuousAt.comp
      (f := fun z : (ℝ × Plane) × (ℝ × Plane) => z.2)
      (x := ((t, q), (x, q))) continuousAt_snd
  have hne' : ∀ᶠ z : (ℝ × Plane) × (ℝ × Plane) in 𝓝 ((t, q), (x, q)),
      scalarGradientSlope φ z.1 ≠ scalarGradientSlope ψ z.2 := by
    simpa only [sub_ne_zero] using
      (hcφ.sub hcψ).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨c, hc, hcb⟩ := Metric.mem_nhds_iff.mp hne'
  let r := min a (min b (c / 2))
  have hr : 0 < r := lt_min ha (lt_min hb (half_pos hc))
  have hra : r ≤ a := min_le_left _ _
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r < c := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hc)
  refine ⟨r, hr, σφ, σψ, hσφ, hσψ,
    (closedBall_subset_closedBall hra).trans hUa,
    (closedBall_subset_closedBall hrb).trans hVb,
    fun z hz => hφa z (closedBall_subset_closedBall hra hz),
    fun z hz => hψb z (closedBall_subset_closedBall hrb hz), ?_, ?_⟩
  · intro v hv
    exact ⟨(hmφ v (closedBall_subset_closedBall hra hv)).mono
      (closedBall_subset_closedBall hra),
      (hmψ v (closedBall_subset_closedBall hrb hv)).mono
        (closedBall_subset_closedBall hrb)⟩
  · intro z hz w hw
    apply hcb (a := (z, w))
    apply closedBall_subset_ball hrc
    rw [← closedBall_prod_same]
    exact ⟨hz, hw⟩

namespace ProjectionModel
variable {d : ℕ} (D : ProjectionModel d)

/-- The curve family has a rotating, nonzero head gradient at some
interior time for every admissible two-slice parameter. -/
theorem exists_twoSliceCurves_nonstationary_point
    (j : Fin (d + 1)) (hj : j ≠ 0) (q : Plane)
    (hq : twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius) :
    ∃ t ∈ Ioo D.I.left D.I.right,
      scalarHeadDerivative (D.twoSliceCurves j) (t, q) ≠ 0 ∧
      deriv (fun s => scalarGradientSlope (D.twoSliceCurves j) (s, q)) t ≠ 0 := by
  let w := twoParameterInsert D.base.2 j q
  obtain ⟨t, ht, hdet, hcol⟩ :=
    D.exists_interior_pairVariationDet_and_column_ne_zero j 0 hj w hq
  have htI : t ∈ D.I.carrier := ⟨ht.1.le, ht.2.le⟩
  refine ⟨t, ht, ?_, ?_⟩
  · rwa [D.twoSliceCurves_headDerivative j (t, q) htI hq]
  · have he : (fun s => scalarGradientSlope (D.twoSliceCurves j) (s, q)) =ᶠ[𝓝 t]
        (fun s => D.variationColumn j (s, w) / D.variationColumn 0 (s, w)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [scalarGradientSlope,
        D.twoSliceCurves_headDerivative j (s, q) ⟨hs.1.le, hs.2.le⟩ hq,
        D.twoSliceCurves_tailDerivative j (s, q) ⟨hs.1.le, hs.2.le⟩ hq]
    rw [he.deriv_eq]
    exact D.deriv_variation_ratio_ne_zero j 0 w hq t htI hcol hdet

/-- The rotating curve gradient can also avoid any prescribed centre
direction, at the same auxiliary parameter. -/
theorem exists_twoSliceCurves_nonstationary_point_ne_slope
    (j : Fin (d + 1)) (hj : j ≠ 0) (q : Plane)
    (hq : twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius) (c : ℝ) :
    ∃ t ∈ Ioo D.I.left D.I.right,
      scalarHeadDerivative (D.twoSliceCurves j) (t, q) ≠ 0 ∧
      deriv (fun s => scalarGradientSlope (D.twoSliceCurves j) (s, q)) t ≠ 0 ∧
      scalarGradientSlope (D.twoSliceCurves j) (t, q) ≠ c := by
  obtain ⟨t, ht, hh, hd⟩ := D.exists_twoSliceCurves_nonstationary_point j hj q hq
  let U : Set (ℝ × Plane) := Ioo D.I.left D.I.right ×ˢ
    (twoParameterInsert D.base.2 j ⁻¹' ball D.base.2 D.radius)
  have hU : IsOpen U := isOpen_Ioo.prod (isOpen_ball.preimage
    (continuousOn_univ.mp (twoParameterInsert_analytic D.base.2 j).continuousOn))
  obtain ⟨r, hr, σ, _, hsub, hbox, _⟩ :=
    exists_scalarGradientSlope_monotone_patch hU (show (t, q) ∈ U from ⟨ht, hq⟩)
      (D.twoSliceCurves_analyticAt j (t, q) ⟨ht.1.le, ht.2.le⟩ hq) hh hd
  obtain ⟨s, hs, hne⟩ := exists_mem_ne_of_deriv_ne_zero (ball_mem_nhds t hr) hd c
  have hpair : (s, q) ∈ closedBall (t, q) r := by
    rw [← closedBall_prod_same]
    exact ⟨ball_subset_closedBall hs, mem_closedBall_self hr.le⟩
  exact ⟨s, (hsub hpair).1, (hbox (s, q) hpair).2.1,
    (mul_ne_zero_iff.mp (hbox (s, q) hpair).2.2.ne').2, hne⟩

end ProjectionModel
end PlanarNikodym
