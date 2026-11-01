import PlanarNikodym.Analysis.Fourier.UniformTimeSliceSquareSum
import PlanarNikodym.Analysis.Localization.ActiveTimeSliceRegularity
import PlanarNikodym.Geometry.MovingChartPhaseRegularity

/-! The pure chart conditions used by the proved square-sum theorem are
constructed from the actual moving-chart geometry of A4.2. No source,
target, inverse, regularity or Jacobian certificate is added as an
unproved analytic input. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.timeSliceChartGeometry_retained {d : ℕ} (G : Family 2 d)
    (hm : 2 ≤ d + 2) (σ : Fin 2 ↪ Fin (d + 2))
    (E : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (he : ∀ x, E x = (x.1, G.movingLowerJetMap hm σ x))
    (hea : AnalyticOnNhd ℝ E E.source) (hei : AnalyticOnNhd ℝ E.symm E.target)
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hK : IsCompact K) (hKS : K ⊆ E.source)
    {β : ℝ} (hJac : ∀ x ∈ K, β ≤ |fiberChartJacobian E x|)
    (ψ : Cutoff d) (L : Set (ℝ × Parameters 2 d))
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (v : ℕ → Aux (d + 2))
    (hspan : ∀ i : ℕ, ∀ x ∈ tsupport (scaleTimeLocalizedCutoff ψ b δ i),
      ∀ τ ∈ Icc (-1 : ℝ) 1,
        ∀ s ∈ uIcc (b + (i : ℝ) * δ) (b + (i : ℝ) * δ + δ * τ), (s, x.2) ∈ L) :
    let hfirst : ∀ x, (E x).1 = x.1 := fun x => by rw [he]
    TimeSliceChartGeometry G E σ (fun x => (ψ (x.2.1, x.1) : ℂ))
      (Prod.swap '' L) (E '' K) b δ N β v
      (fun i => retainedParameterFiber E hfirst (b + (i : ℝ) * δ, v i))
      (fun i => {z | ((b + (i : ℝ) * δ, v i), z) ∈ K}) hm := by
  dsimp only
  intro i _hi
  let q : ℝ × Aux (d + 2) := (b + (i : ℝ) * δ, v i)
  have hfirst : ∀ x, (E x).1 = x.1 := fun x => by rw [he]
  let e := retainedParameterFiber E hfirst q
  have heFiber : ∀ z, e z = G.lowerCinematicJetMap hm σ q.1 q.2 z := by
    intro z
    change (E (q, z)).2 = _
    rw [he]
    rfl
  refine ⟨heFiber, (retainedParameterFiber_analytic hfirst hea hei q).1, ?_,
    hK.isClosed.measurableSet.preimage (continuous_const.prodMk continuous_id).measurable,
    fun z hz => hKS hz, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact G.analyticAt_of_moving_linear_chart hm σ E he (hea (q, z) hz)
  · intro z hz
    change β ≤ |fiberChartJacobian E (q, z)|
    exact hJac (q, z) hz
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨(q, z), hz, ?_⟩
    exact Prod.ext (hfirst (q, z)) rfl
  · intro y _hy
    rfl
  · intro y _hy τ η p hactive
    have hactive' : (ψ (b + (i : ℝ) * δ + δ * τ, p) : ℂ) *
        (timePartitionWindow τ : ℂ) ≠ 0 := hactive
    obtain ⟨hc, ht⟩ := active_timeSlice_center_endpoints ψ b hδ i L (hspan i) p τ hactive'
    exact ⟨⟨(q.1, p), hc, rfl⟩, ⟨(q.1 + δ * τ, p), ht, rfl⟩⟩

end PlanarNikodym
