import PlanarNikodym.Projection.LocalWisewellScaling
import PlanarNikodym.Projection.StationaryConstructionTransfer

/-! Corollary 3.2 for actual scalar normal forms, and the stationary
branch of §7.3.  The successful parameter interval and null set are
constructed here, rather than supplied as hypotheses. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PlanarNikodym.ProjectionModel

variable {d : ℕ} (D : ProjectionModel d)

/-- The bounded factorial construction applies to an arbitrarily small
parameter neighbourhood in the original analytic model.  It produces
both a positive-measure interval of successful first parameters and a
compact null set containing the full selected time segments. -/
theorem exists_compact_null_twoSlice_curves (j : Fin (d + 1)) (hj : j ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K : Set ℝ, ∃ E : Set Plane,
      MeasurableSet A ∧ 0 < volume A ∧ A ⊆ ball (D.base.2 0) ε ∧
      IsCompact K ∧ 0 < volume K ∧ K ⊆ D.I.carrier ∧
      IsCompact E ∧ volume E = 0 ∧
      ∀ y ∈ A, ∃ s ∈ ball (D.base.2 j) ε,
        twoParameterInsert D.base.2 j (y, s) ∈ ball D.base.2 D.radius ∧
        (fun t => (t, D.h t (twoParameterInsert D.base.2 j (y, s)))) '' K ⊆ E := by
  obtain ⟨t, _, r, hr, _, _, hbox⟩ := D.exists_twoSlice_wisewell_patch j hj
  let a : ℝ := min r (ε / 2)
  have ha : 0 < a := lt_min hr (half_pos hε)
  have har : a ≤ r := min_le_left _ _
  have haε : a < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  have hsmall : closedBall (t, (D.base.2 0, D.base.2 j)) a ⊆
      closedBall (t, (D.base.2 0, D.base.2 j)) r :=
    closedBall_subset_closedBall har
  obtain ⟨δ, hδ, hδa, E, hEc, hE0, hE⟩ :=
    Wisewell.exists_compact_null_curves_on_regular_box (D.twoSliceCurves j) t
      (D.base.2 0, D.base.2 j) a ha
      (fun p hp => (hbox p (hsmall hp)).2.2.1)
      (fun p hp => (hbox p (hsmall hp)).2.2.2.1)
  let A : Set ℝ := Icc (D.base.2 0) (D.base.2 0 + δ)
  let K : Set ℝ := closedBall t (a / 2)
  have hKA (u : ℝ) (hu : u ∈ K) (q : Plane) (hq : q ∈ closedBall
      (D.base.2 0, D.base.2 j) a) :
      (u, q) ∈ closedBall (t, (D.base.2 0, D.base.2 j)) r := by
    apply hsmall
    rw [← closedBall_prod_same]
    exact ⟨closedBall_subset_closedBall (by linarith) hu, hq⟩
  have hAY : A ⊆ ball (D.base.2 0) ε := by
    intro y hy
    rw [mem_ball, Real.dist_eq]
    rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
    exact (show y - D.base.2 0 ≤ δ by linarith [hy.2]).trans_lt (hδa.trans haε)
  have htK : t ∈ K := mem_closedBall_self (half_pos ha).le
  refine ⟨A, K, E, measurableSet_Icc, ?_, hAY, isCompact_closedBall _ _, ?_, ?_,
    hEc, hE0, ?_⟩
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  · rw [Real.volume_closedBall]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  · intro u hu
    exact ⟨(hbox (u, (D.base.2 0, D.base.2 j))
      (hKA u hu _ (mem_closedBall_self ha.le))).1.1.le,
      (hbox (u, (D.base.2 0, D.base.2 j))
      (hKA u hu _ (mem_closedBall_self ha.le))).1.2.le⟩
  · intro y hy
    obtain ⟨s, hs, hcover⟩ := hE y hy
    have hyA : y ∈ closedBall (D.base.2 0) a := by
      rw [mem_closedBall, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
      exact (show y - D.base.2 0 ≤ δ by linarith [hy.2]).trans hδa.le
    have hq : (y, s) ∈ closedBall (D.base.2 0, D.base.2 j) a := by
      rw [← closedBall_prod_same]
      exact ⟨hyA, mem_closedBall.mpr (mem_ball.mp hs).le⟩
    refine ⟨s, lt_of_lt_of_le hs (by exact haε.le), ?_, hcover⟩
    exact (hbox (t, (y, s)) (hKA t htK _ hq)).2.1

/-- Selected scalar curves in a compact null set have a genuine positive
length set of hit times.  This version exposes the original parameters
needed by the stationary centre-trace transfer. -/
theorem exists_null_twoSlice_positive_hitTimes (j : Fin (d + 1)) (hj : j ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℝ, ∃ E : Set Plane,
      MeasurableSet A ∧ 0 < volume A ∧ A ⊆ ball (D.base.2 0) ε ∧
      IsCompact E ∧ volume E = 0 ∧
      ∀ y ∈ A, ∃ s ∈ ball (D.base.2 j) ε,
        twoParameterInsert D.base.2 j (y, s) ∈ ball D.base.2 D.radius ∧
        0 < volume (D.hitTimes (twoParameterInsert D.base.2 j (y, s)) E) := by
  obtain ⟨A, K, E, hAm, hApos, hAY, _, hKpos, hKI, hEc, hE0, hsel⟩ :=
    D.exists_compact_null_twoSlice_curves j hj ε hε
  refine ⟨A, E, hAm, hApos, hAY, hEc, hE0, ?_⟩
  intro y hy
  obtain ⟨s, hs, hq, hcover⟩ := hsel y hy
  refine ⟨s, hs, hq, hKpos.trans_le (measure_mono ?_)⟩
  intro t ht
  exact ⟨hKI ht, hcover (mem_image_of_mem _ ht)⟩

/-- The stationary branch has an actual Borel null set with a centre
trace of positive inner measure.  Stationarity is the sole branch
hypothesis; neither successful parameters nor a Wisewell selector are
assumed. -/
theorem exists_null_set_of_twoSlice_stationary (j : Fin (d + 1)) (hj : j ≠ 0)
    (hst : ∀ q : Plane,
      twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius →
      ∀ x ∈ ball D.base.1 D.radius,
        deriv (fun a => scalarGradientSlope (D.twoSliceCenters j) (a, q)) x = 0) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) := by
  obtain ⟨r, hr, hXB, hQB, hh⟩ := D.exists_twoSlice_center_patch j hj
  obtain ⟨A, E, hAm, hApos, hAY, hEc, hE0, hhit⟩ :=
    D.exists_null_twoSlice_positive_hitTimes j hj r hr
  refine ⟨E, hEc.measurableSet, hE0, ?_⟩
  exact D.incidenceTrace_hasPositivePart_of_twoSlice_stationary j hj E
    isOpen_ball (convex_ball D.base.1 r).isPreconnected isOpen_ball
    isOpen_ball (convex_ball (D.base.2 j) r).isPreconnected
    (mem_ball_self hr) hXB hQB (fun p hp => hh p.1 hp.1 p.2 hp.2)
    (fun q hq x hx => hst q (hQB q hq) x (hXB hx))
    (D.base.2 j) (mem_ball_self hr) hAm hAY hApos
    (fun y hy => by
      obtain ⟨s, hs, _, ht⟩ := hhit y hy
      exact ⟨s, hs, ht⟩)

end PlanarNikodym.ProjectionModel
