import PlanarNikodym.Projection.ProjectionTwoSlice
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! The regularity and scalar Jacobian hypotheses for the local Wisewell
construction, derived from an actual two-parameter slice.

The closed balls below are closed boxes for the product maximum norm.
The null-set selector in Wisewell's theorem remains to be constructed. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff NNReal
namespace PlanarNikodym.ProjectionModel

variable {d : ℕ} (D : ProjectionModel d)

/-- The two-column determinant is an actual nonstationarity test in a
projective coordinate whenever the denominator column is nonzero. -/
theorem deriv_variation_ratio_ne_zero (i j : Fin (d + 1))
    (w : Aux (d + 1)) (hw : w ∈ ball D.base.2 D.radius)
    (t : ℝ) (ht : t ∈ D.I.carrier)
    (hcol : D.variationColumn j (t, w) ≠ 0)
    (hdet : D.pairVariationDet i j (t, w) ≠ 0) :
    deriv (fun s => D.variationColumn i (s, w) / D.variationColumn j (s, w)) t ≠ 0 := by
  have hi := ((D.variationColumn_analyticAt ⟨ht, hw⟩ i).comp
    (f := fun s : ℝ => (s, w)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hj := ((D.variationColumn_analyticAt ⟨ht, hw⟩ j).comp
    (f := fun s : ℝ => (s, w)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  change DifferentiableAt ℝ (fun s => D.variationColumn i (s, w)) t at hi
  change DifferentiableAt ℝ (fun s => D.variationColumn j (s, w)) t at hj
  rw [deriv_fun_div hi hj hcol]
  apply div_ne_zero
  · have hdet' : D.variationColumn i (t, w) * deriv (fun s => D.variationColumn j (s, w)) t -
        D.variationColumn j (t, w) * deriv (fun s => D.variationColumn i (s, w)) t ≠ 0 := by
      simpa only [pairVariationDet,
        timeDerivative_eq_iteratedDeriv 1 (t, w) (D.variationColumn_analyticAt ⟨ht, hw⟩ i),
        timeDerivative_eq_iteratedDeriv 1 (t, w) (D.variationColumn_analyticAt ⟨ht, hw⟩ j),
        iteratedDeriv_one] using hdet
    intro hz
    apply hdet'
    nlinarith
  · exact pow_ne_zero 2 hcol

/-- Normalization supplies an actual centre-gradient patch for the
stationary branch; the nonzero first component need not be assumed at
the start of the construction. -/
theorem exists_twoSlice_center_patch (j : Fin (d + 1)) (hj : j ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      ball D.base.1 r ⊆ ball D.base.1 D.radius ∧
      (∀ q ∈ ball (D.base.2 0) r ×ˢ ball (D.base.2 j) r,
        twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius) ∧
      ∀ x ∈ ball D.base.1 r,
        ∀ q ∈ ball (D.base.2 0) r ×ˢ ball (D.base.2 j) r,
          scalarHeadDerivative (D.twoSliceCenters j) (x, q) ≠ 0 := by
  let q₀ : Plane := (D.base.2 0, D.base.2 j)
  let p₀ : ℝ × Plane := (D.base.1, q₀)
  have hq₀ : twoParameterInsert D.base.2 j q₀ = D.base.2 :=
    twoParameterInsert_base _ _
  have hqa := (twoParameterInsert_analytic D.base.2 j) q₀ (mem_univ _)
  have hqB : ball D.base.2 D.radius ∈ 𝓝 (twoParameterInsert D.base.2 j q₀) := by
    rw [hq₀]
    exact ball_mem_nhds _ D.radius_pos
  obtain ⟨a, ha, hqaB⟩ := Metric.mem_nhds_iff.mp (hqa.continuousAt.preimage_mem_nhds hqB)
  have hQB (q : Plane) (hq : q ∈ ball (D.base.2 0) a ×ˢ ball (D.base.2 j) a) :
      twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius := by
    apply hqaB
    rw [← ball_prod_same]
    exact hq
  have hψ₀ : AnalyticAt ℝ (D.twoSliceCenters j) p₀ :=
    D.twoSliceCenters_analyticAt j p₀ (mem_ball_self D.radius_pos)
      (by rw [hq₀]; exact mem_ball_self D.radius_pos)
  have hhead₀ : scalarHeadDerivative (D.twoSliceCenters j) p₀ = 1 :=
    (scalar_parameter_derivatives_of_normalize isOpen_ball isOpen_ball D.base.1 q₀
      ⟨mem_ball_self ha, mem_ball_self ha⟩ hψ₀.differentiableAt
        (fun q hq => D.twoSliceCenters_normalize j hj q (hQB q hq))).1
  let Φ : (ℝ × Plane) → ℝ × Aux (d + 1) :=
    fun p => (p.1, twoParameterInsert D.base.2 j p.2)
  have hΦ : AnalyticAt ℝ Φ p₀ :=
    analyticAt_fst.prod (((twoParameterInsert_analytic D.base.2 j) p₀.2
      (mem_univ _)).comp analyticAt_snd)
  have hΦ₀ : Φ p₀ = D.base := by simp [Φ, p₀, q₀]
  have hgood : ∀ᶠ p in 𝓝 p₀,
      p.1 ∈ ball D.base.1 D.radius ∧
      twoParameterInsert D.base.2 j p.2 ∈ ball D.base.2 D.radius ∧
      scalarHeadDerivative (D.twoSliceCenters j) p ≠ 0 := by
    have hdom : ∀ᶠ p in 𝓝 p₀,
        Φ p ∈ ball D.base.1 D.radius ×ˢ ball D.base.2 D.radius := by
      apply hΦ.continuousAt.preimage_mem_nhds
      rw [hΦ₀]
      exact (isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨mem_ball_self D.radius_pos, mem_ball_self D.radius_pos⟩
    filter_upwards [hdom, (scalarHeadDerivative_analyticAt hψ₀).continuousAt.eventually_ne
      (show scalarHeadDerivative (D.twoSliceCenters j) p₀ ≠ 0 by rw [hhead₀]; norm_num)]
      with p hp hhead
    exact ⟨hp.1, hp.2, hhead⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hbox (x : ℝ) (hx : x ∈ ball D.base.1 r) (q : Plane)
      (hq : q ∈ ball (D.base.2 0) r ×ˢ ball (D.base.2 j) r) :
      x ∈ ball D.base.1 D.radius ∧
      twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius ∧
      scalarHeadDerivative (D.twoSliceCenters j) (x, q) ≠ 0 := by
    apply hball (a := (x, q))
    rw [← ball_prod_same, ← ball_prod_same]
    exact ⟨hx, hq⟩
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · intro x hx
    exact (hbox x hx q₀ ⟨mem_ball_self hr, mem_ball_self hr⟩).1
  · intro q hq
    exact (hbox D.base.1 (mem_ball_self hr) q hq).2.1
  · intro x hx q hq
    exact (hbox x hx q hq).2.2

/-- Fixing all unused coordinates does preserve the regularity and
nonvanishing scalar Jacobian needed for Corollary 3.2, after restricting
to a genuine closed product neighbourhood. The derivative is Lipschitz
on the whole closed box, and the two-column rotation test is nonzero
there as well. -/
theorem exists_twoSlice_wisewell_patch (j : Fin (d + 1)) (hj : j ≠ 0) :
    ∃ t ∈ Ioo D.I.left D.I.right, ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ≥0,
      LipschitzOnWith K (fderiv ℝ (D.twoSliceCurves j))
        (closedBall (t, (D.base.2 0, D.base.2 j)) r) ∧
      ∀ p ∈ closedBall (t, (D.base.2 0, D.base.2 j)) r,
        p.1 ∈ Ioo D.I.left D.I.right ∧
        twoParameterInsert D.base.2 j p.2 ∈ ball D.base.2 D.radius ∧
        AnalyticAt ℝ (D.twoSliceCurves j) p ∧
        scalarTailDerivative (D.twoSliceCurves j) p ≠ 0 ∧
        D.pairVariationDet 0 j (p.1, twoParameterInsert D.base.2 j p.2) ≠ 0 := by
  have hb : D.base.2 ∈ ball D.base.2 D.radius := mem_ball_self D.radius_pos
  obtain ⟨t, ht, hdet, hcol⟩ :=
    D.exists_interior_pairVariationDet_and_column_ne_zero 0 j hj.symm D.base.2 hb
  let p₀ : ℝ × Plane := (t, (D.base.2 0, D.base.2 j))
  let Φ : (ℝ × Plane) → ℝ × Aux (d + 1) :=
    fun p => (p.1, twoParameterInsert D.base.2 j p.2)
  have hΦ : AnalyticAt ℝ Φ p₀ :=
    analyticAt_fst.prod (((twoParameterInsert_analytic D.base.2 j) p₀.2
      (mem_univ _)).comp analyticAt_snd)
  have hΦ₀ : Φ p₀ = (t, D.base.2) := by simp [Φ, p₀]
  have hq₀ : twoParameterInsert D.base.2 j p₀.2 ∈ ball D.base.2 D.radius := by
    simpa only [p₀, twoParameterInsert_base] using hb
  have ha : AnalyticAt ℝ (D.twoSliceCurves j) p₀ :=
    D.twoSliceCurves_analyticAt j p₀ ⟨ht.1.le, ht.2.le⟩ hq₀
  have htail : scalarTailDerivative (D.twoSliceCurves j) p₀ ≠ 0 := by
    rw [D.twoSliceCurves_tailDerivative j p₀ ⟨ht.1.le, ht.2.le⟩ hq₀]
    simpa only [p₀, twoParameterInsert_base] using hcol
  have hrot : AnalyticAt ℝ (fun p => D.pairVariationDet 0 j (Φ p)) p₀ := by
    apply (D.pairVariationDet_analyticAt (x := (t, D.base.2))
      ⟨⟨ht.1.le, ht.2.le⟩, hb⟩ 0 j).comp_of_eq hΦ hΦ₀
  have hrot₀ : D.pairVariationDet 0 j (Φ p₀) ≠ 0 := by rwa [hΦ₀]
  have hC : ContDiffAt ℝ 1 (fderiv ℝ (D.twoSliceCurves j)) p₀ :=
    ha.fderiv.contDiffAt
  obtain ⟨K, V, hV, hLip⟩ := hC.exists_lipschitzOnWith
  have hgood : ∀ᶠ p in 𝓝 p₀,
      p ∈ V ∧ p.1 ∈ Ioo D.I.left D.I.right ∧
      twoParameterInsert D.base.2 j p.2 ∈ ball D.base.2 D.radius ∧
      scalarTailDerivative (D.twoSliceCurves j) p ≠ 0 ∧
      D.pairVariationDet 0 j (Φ p) ≠ 0 := by
    have hΦdom : ∀ᶠ p in 𝓝 p₀,
        Φ p ∈ Ioo D.I.left D.I.right ×ˢ ball D.base.2 D.radius := by
      apply hΦ.continuousAt.preimage_mem_nhds
      rw [hΦ₀]
      exact (isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨ht, hb⟩
    filter_upwards [hV, hΦdom,
      (scalarTailDerivative_analyticAt ha).continuousAt.eventually_ne htail,
      hrot.continuousAt.eventually_ne hrot₀] with p hp hpdom hptail hprot
    exact ⟨hp, hpdom.1, hpdom.2, hptail, hprot⟩
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hclosed : closedBall p₀ (a / 2) ⊆ ball p₀ a :=
    closedBall_subset_ball (half_lt_self ha)
  have hclosedV : closedBall p₀ (a / 2) ⊆ V :=
    fun p hp => (hball (hclosed hp)).1
  refine ⟨t, ht, a / 2, half_pos ha, K, hLip.mono hclosedV, ?_⟩
  intro p hp
  obtain ⟨_, hpI, hpB, hptail, hprot⟩ := hball (hclosed hp)
  exact ⟨hpI, hpB, D.twoSliceCurves_analyticAt j p ⟨hpI.1.le, hpI.2.le⟩ hpB,
    hptail, hprot⟩

end PlanarNikodym.ProjectionModel
