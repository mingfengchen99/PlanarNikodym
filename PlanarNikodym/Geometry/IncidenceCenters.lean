import PlanarNikodym.Classification.CoveredTransfer
import PlanarNikodym.Geometry.CoordinateMeasure

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace PlanarNikodym

def Family.incidenceCenters {d : ℕ} (G : Family 2 d) (U : Set (Parameters 2 d))
    (E : Set Plane) : Set (Base 2) :=
  {z | ∃ u, (z, u) ∈ U ∧ 0 < Measure.hausdorffMeasure 1 (G.curve (z, u) ∩ E)}

theorem Family.incidenceCenters_mono {d e : ℕ} (G : Family 2 d) (H : Family 2 e)
    (U : Set (Parameters 2 d)) (V : Set (Parameters 2 e))
    (he : ∀ z, G.curvesAtOn U z ⊆ H.curvesAtOn V z) (E : Set Plane) :
    G.incidenceCenters U E ⊆ H.incidenceCenters V E := by
  rintro z ⟨u, hu, hp⟩
  obtain ⟨v, hv, hc⟩ := he z ⟨u, hu, rfl⟩
  exact ⟨v, hv, hc ▸ hp⟩

theorem Family.no_nikodym_of_incidence_null {d : ℕ} (G : Family 2 d)
    (h : ∀ E : Set Plane, MeasurableSet E → volume E = 0 →
      volume (G.incidenceCenters G.W E) = 0) : ¬ G.AdmitsNikodym := by
  rintro ⟨E, F, hE, _, hE0, hFp, hf⟩
  have hsub : F ⊆ G.incidenceCenters G.W E := hf
  exact hFp.ne' (measure_mono_null hsub (h E hE hE0))

theorem Family.no_massive_of_incidence_null {d : ℕ} (G : Family 2 d) (ha : G.IsSmooth)
    (h : ∀ E : Set Plane, MeasurableSet E → volume E = 0 →
      volume (G.incidenceCenters G.W E) = 0) : ¬ G.HasMassiveCurveReuse := by
  intro hmass
  exact G.no_nikodym_of_incidence_null h (G.admitsNikodym_of_hasMassiveCurveReuse ha hmass)

theorem Family.hasLocalCurveReuse_of_all {d : ℕ} (G : Family 2 d)
    (hW : IsOpen G.W) (hWne : G.W.Nonempty)
    (h : ∀ p ∈ G.W, G.LocallyReused p) : G.HasLocalCurveReuse := by
  obtain ⟨q, hq⟩ := hWne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hq)
  refine ⟨ball q.1 r, ?_, isOpen_ball.measurableSet,
    isOpen_ball.measure_pos (μ := volume) ⟨q.1, mem_ball_self hr⟩⟩
  intro z hz
  refine ⟨q.2, h (z, q.2) (hball ?_)⟩
  rw [← ball_prod_same]
  exact ⟨hz, mem_ball_self hr⟩

end PlanarNikodym
