import PlanarNikodym.Projection.LocalWisewellConstruction
import PlanarNikodym.Projection.NonstationaryProjectionGeometry

/-! Actual branch reduction for the scalar projection construction.

Stationarity is tested only on the regular neighbourhood provided by
normalization. If it holds, the already constructed Wisewell set gives
the required null set. Otherwise we obtain actual regular nonstationary
points for both projection families at the same auxiliary parameter,
with distinct slopes. The remaining branch requires a prescribed-
projection selection; no such selection is assumed or asserted here.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology

namespace PlanarNikodym.ProjectionModel
variable {d : ℕ} (D : ProjectionModel d)

/-- Local stationarity on a regular normalized box suffices for the
actual null-set construction. No global stationarity is required. -/
theorem exists_null_set_of_twoSlice_stationary_on_patch
    (j : Fin (d + 1)) (hj : j ≠ 0) (r : ℝ) (hr : 0 < r)
    (hXB : ball D.base.1 r ⊆ ball D.base.1 D.radius)
    (hQB : ∀ q ∈ ball (D.base.2 0) r ×ˢ ball (D.base.2 j) r,
      twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius)
    (hh : ∀ x ∈ ball D.base.1 r,
      ∀ q ∈ ball (D.base.2 0) r ×ˢ ball (D.base.2 j) r,
        scalarHeadDerivative (D.twoSliceCenters j) (x, q) ≠ 0)
    (hst : ∀ q ∈ ball (D.base.2 0) r ×ˢ ball (D.base.2 j) r,
      ∀ x ∈ ball D.base.1 r,
        deriv (fun a => scalarGradientSlope (D.twoSliceCenters j) (a, q)) x = 0) :
    ∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E) := by
  obtain ⟨A, E, hAm, hApos, hAY, hEc, hE0, hhit⟩ :=
    D.exists_null_twoSlice_positive_hitTimes j hj r hr
  refine ⟨E, hEc.measurableSet, hE0, ?_⟩
  exact D.incidenceTrace_hasPositivePart_of_twoSlice_stationary j hj E
    isOpen_ball (convex_ball D.base.1 r).isPreconnected isOpen_ball
    isOpen_ball (convex_ball (D.base.2 j) r).isPreconnected
    (mem_ball_self hr) hXB hQB (fun p hp => hh p.1 hp.1 p.2 hp.2) hst
    (D.base.2 j) (mem_ball_self hr) hAm hAY hApos
    (fun y hy => by
      obtain ⟨s, hs, _, ht⟩ := hhit y hy
      exact ⟨s, hs, ht⟩)

/-- Every valid two-slice either already has the required Borel null
set, or has a regular nonstationary centre point. The regular point is
chosen inside the normalized patch, not at a possibly singular witness
of global nonstationarity. -/
theorem exists_null_set_or_twoSlice_nonstationary_point
    (j : Fin (d + 1)) (hj : j ≠ 0) :
    (∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E)) ∨
    ∃ x : ℝ, ∃ q : Plane,
      x ∈ ball D.base.1 D.radius ∧
      twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius ∧
      scalarHeadDerivative (D.twoSliceCenters j) (x, q) ≠ 0 ∧
      deriv (fun a => scalarGradientSlope (D.twoSliceCenters j) (a, q)) x ≠ 0 := by
  classical
  obtain ⟨r, hr, hXB, hQB, hh⟩ := D.exists_twoSlice_center_patch j hj
  by_cases hst : ∀ q ∈ ball (D.base.2 0) r ×ˢ ball (D.base.2 j) r,
      ∀ x ∈ ball D.base.1 r,
        deriv (fun a => scalarGradientSlope (D.twoSliceCenters j) (a, q)) x = 0
  · exact Or.inl (D.exists_null_set_of_twoSlice_stationary_on_patch j hj r hr hXB hQB hh hst)
  · push Not at hst
    obtain ⟨q, hq, x, hx, hd⟩ := hst
    exact Or.inr ⟨x, q, hXB hx, hQB q hq, hh x hx q hq, hd⟩

/-- For arbitrary positive auxiliary dimension, a valid slice is chosen
and the stationary branch is actually discharged. The other branch has
two regular rotating directions at the same parameter and with distinct
slopes; the local patch theorem then supplies separated closed boxes. -/
theorem exists_null_set_or_separated_twoSlice_points (hd : 0 < d) :
    (∃ E : Set Plane, MeasurableSet E ∧ volume E = 0 ∧
      HasPositivePart volume (D.incidenceTrace E)) ∨
    ∃ j : Fin (d + 1), ∃ t x : ℝ, ∃ q : Plane,
      j ≠ 0 ∧ t ∈ Ioo D.I.left D.I.right ∧ x ∈ ball D.base.1 D.radius ∧
      twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius ∧
      scalarHeadDerivative (D.twoSliceCurves j) (t, q) ≠ 0 ∧
      scalarHeadDerivative (D.twoSliceCenters j) (x, q) ≠ 0 ∧
      deriv (fun s => scalarGradientSlope (D.twoSliceCurves j) (s, q)) t ≠ 0 ∧
      deriv (fun s => scalarGradientSlope (D.twoSliceCenters j) (s, q)) x ≠ 0 ∧
      scalarGradientSlope (D.twoSliceCurves j) (t, q) ≠
        scalarGradientSlope (D.twoSliceCenters j) (x, q) := by
  let j : Fin (d + 1) := ⟨1, by omega⟩
  have hj : j ≠ 0 := by intro h; have := congrArg Fin.val h; simp [j] at this
  rcases D.exists_null_set_or_twoSlice_nonstationary_point j hj with hE | ⟨x, q, hx, hq, hh, hδ⟩
  · exact Or.inl hE
  · obtain ⟨t, ht, hhead, hderiv, hne⟩ :=
      D.exists_twoSliceCurves_nonstationary_point_ne_slope j hj q hq
        (scalarGradientSlope (D.twoSliceCenters j) (x, q))
    exact Or.inr ⟨j, t, x, q, hj, ht, hx, hq, hhead, hh, hderiv, hδ, hne⟩

end PlanarNikodym.ProjectionModel
