import PlanarNikodym.Projection.ProjectedSweepTransfer

/-! The full centre targets in the prescribed-projection argument.

On an open regular parameter patch, the joint set of projected values
is open and has positive planar measure. Its section integral is
therefore strictly positive. These are properties of the actual maps
and full target patches; a selection preserving those targets remains
the separate prescribed-projection construction.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PlanarNikodym

/-- A nonzero head derivative makes the joint projection image of an
open time-parameter set open. A two-dimensional analytic chart with the
tail coordinate fixed supplies a neighbourhood of each image point. -/
theorem scalarProjectionSweep_isOpen
    (φ : ℝ × Plane → ℝ) (X : Set ℝ) (G : Set Plane)
    (hX : IsOpen X) (hG : IsOpen G)
    (hφ : AnalyticOnNhd ℝ φ (X ×ˢ G))
    (hh : ∀ p ∈ X ×ˢ G, scalarHeadDerivative φ p ≠ 0) :
    IsOpen (scalarProjectionSweep (fun x q => φ (x, q)) X G) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro c ⟨hc, q, hq, heq⟩
  let g : Plane → ℝ := fun z => φ (z.1, (z.2, q.2))
  let f : Plane → Plane := fun z => (z.1, g z)
  let U : Set Plane := {z | z.1 ∈ X ∧ (z.2, q.2) ∈ G}
  have hg : AnalyticAt ℝ g (c.1, q.1) :=
    (hφ (c.1, q) ⟨hc, hq⟩).comp
      (f := fun z : Plane => (z.1, (z.2, q.2)))
      (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const))
  have hf : AnalyticAt ℝ f (c.1, q.1) := analyticAt_fst.prod hg
  have hi : (fderiv ℝ f (c.1, q.1)).IsInvertible := by
    apply triangular_fderiv_isInvertible g (c.1, q.1) hg.differentiableAt
    rw [scalar_centerChart_vertical_derivative φ (c.1, q.1) q.2
      (hφ (c.1, q) ⟨hc, hq⟩).differentiableAt]
    exact hh (c.1, q) ⟨hc, hq⟩
  have hU : IsOpen U := (hX.preimage continuous_fst).inter
    (hG.preimage (continuous_snd.prodMk continuous_const))
  obtain ⟨e, hsource, hsub, he, _, _⟩ :=
    exists_analytic_chart f (c.1, q.1) hf hi U (hU.mem_nhds ⟨hc, hq⟩)
  have hec : e (c.1, q.1) = c := by
    rw [he]
    exact Prod.ext rfl heq
  apply Filter.mem_of_superset (hec ▸ e.open_target.mem_nhds (e.map_source hsource))
  intro y hy
  have hz := hsub (e.map_target hy)
  rw [← e.right_inv hy, he]
  exact ⟨hz.1, ((e.symm y).2, q.2), hz.2, rfl⟩

/-- The full target sweep is nonempty and has positive planar measure. -/
theorem scalarProjectionSweep_volume_pos
    (φ : ℝ × Plane → ℝ) (X : Set ℝ) (G : Set Plane)
    (hX : IsOpen X) (hG : IsOpen G) (hXn : X.Nonempty) (hGn : G.Nonempty)
    (hφ : AnalyticOnNhd ℝ φ (X ×ˢ G))
    (hh : ∀ p ∈ X ×ˢ G, scalarHeadDerivative φ p ≠ 0) :
    0 < volume (scalarProjectionSweep (fun x q => φ (x, q)) X G) := by
  apply (scalarProjectionSweep_isOpen φ X G hX hG hφ hh).measure_pos volume
  obtain ⟨x, hx⟩ := hXn
  obtain ⟨q, hq⟩ := hGn
  exact ⟨(x, φ (x, q)), hx, q, hq, rfl⟩

/-- Positivity of the section integral for the full centre targets is
derived by Fubini from the actual open image, not supplied as an input. -/
theorem lintegral_volume_scalarProjections_pos
    (φ : ℝ × Plane → ℝ) (X : Set ℝ) (G : Set Plane)
    (hX : IsOpen X) (hG : IsOpen G) (hXn : X.Nonempty) (hGn : G.Nonempty)
    (hφ : AnalyticOnNhd ℝ φ (X ×ˢ G))
    (hh : ∀ p ∈ X ×ˢ G, scalarHeadDerivative φ p ≠ 0) :
    0 < ∫⁻ x in X, volume ((fun q => φ (x, q)) '' G) := by
  have hm : NullMeasurableSet (scalarProjectionSweep (fun x q => φ (x, q)) X G) volume :=
    (scalarProjectionSweep_isOpen φ X G hX hG hφ hh).measurableSet.nullMeasurableSet
  rw [← scalarProjectionSweep_volume_eq_lintegral _ X G hX.measurableSet hm]
  exact scalarProjectionSweep_volume_pos φ X G hX hG hXn hGn hφ hh

end PlanarNikodym
