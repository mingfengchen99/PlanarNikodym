import PlanarNikodym.Projection.ProjectionTwoSlice
import PlanarNikodym.Geometry.NullGeometry
import PlanarNikodym.Core.PositiveParts
import Mathlib.MeasureTheory.Measure.Regular

/-! Positive-measure transfer in the stationary branch of §7.3.

The theorem at the end transfers a one-dimensional set of successful
scalar parameters to a positive-inner-measure planar centre trace. The
successful scalar parameters and a null set must still be constructed:
this module does not prove Wisewell's theorem. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace PlanarNikodym

/-- A regular analytic planar map sends a positive-measure Borel set to
a set with a positive-measure compact subset. Injectivity of the map on
the whole domain is unnecessary. -/
theorem hasPositivePart_image_of_analytic_regular
    (f : Plane → Plane) (U A : Set Plane)
    (hf : AnalyticOnNhd ℝ f U)
    (hr : ∀ p ∈ U, (fderiv ℝ f p).IsInvertible)
    (hA : MeasurableSet A) (hAU : A ⊆ U) (hpos : 0 < volume A) :
    HasPositivePart volume (f '' A) := by
  obtain ⟨K, hKA, hKc, hKpos⟩ := hA.exists_lt_isCompact hpos
  have hKU : K ⊆ U := hKA.trans hAU
  have himgc := hKc.image_of_continuousOn (hf.continuousOn.mono hKU)
  refine ⟨f '' K, image_mono hKA, himgc.measurableSet, ?_⟩
  apply pos_iff_ne_zero.mpr
  intro himg0
  have hpre := analytic_regular_preimage_null f U hf volume (f '' K) himg0
  have hKsub : K ⊆ {p | p ∈ U ∧ (fderiv ℝ f p).IsInvertible ∧ f p ∈ f '' K} := by
    intro p hp
    exact ⟨hKU hp, hr p (hKU hp), p, hp, rfl⟩
  exact hKpos.ne' (measure_mono_null hKsub hpre)

/-- The derivative of a triangular planar map is invertible whenever
its second component has nonzero derivative in the vertical direction. -/
theorem triangular_fderiv_isInvertible (g : Plane → ℝ) (p : Plane)
    (hg : DifferentiableAt ℝ g p) (hh : fderiv ℝ g p (0, 1) ≠ 0) :
    (fderiv ℝ (fun p : Plane => (p.1, g p)) p).IsInvertible := by
  let L := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ g p)
  have hL : HasFDerivAt (fun p : Plane => (p.1, g p)) L p :=
    hasFDerivAt_fst.prodMk hg.hasFDerivAt
  have hi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    have hvx : v.1 = 0 := congrArg Prod.fst hv
    have hvg : fderiv ℝ g p v = 0 := congrArg Prod.snd hv
    have he : v = v.2 • ((0, 1) : Plane) := by
      ext <;> simp [hvx]
    have hvy : v.2 = 0 := by
      rw [he, map_smul] at hvg
      exact (mul_eq_zero.mp hvg).resolve_right hh
    exact Prod.ext hvx hvy
  rw [hL.fderiv]
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap
    ⟨hi, LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv, rfl⟩

theorem scalar_centerChart_vertical_derivative
    (ψ : ℝ × Plane → ℝ) (p : Plane) (s₀ : ℝ)
    (hψ : DifferentiableAt ℝ ψ (p.1, (p.2, s₀))) :
    fderiv ℝ (fun q : Plane => ψ (q.1, (q.2, s₀))) p (0, 1) =
      scalarHeadDerivative ψ (p.1, (p.2, s₀)) := by
  have hi : HasFDerivAt (fun q : Plane => (q.1, (q.2, s₀)))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0)) p :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.prodMk (hasFDerivAt_const s₀ p))
  change fderiv ℝ (ψ ∘ fun q : Plane => (q.1, (q.2, s₀))) p (0, 1) = _
  rw [(hψ.hasFDerivAt.comp p hi).fderiv]
  rfl

namespace ProjectionModel
variable {d : ℕ} (D : ProjectionModel d)

/-- The genuine stationary-branch measure transfer. A null set supplied
by the one-dimensional construction is hit by a selected scalar curve
for each `y ∈ A`. Stationarity then permits all `x ∈ X`, and regularity of
the normalized centre chart gives positive inner measure of the trace.
The selected auxiliary value need not be a measurable function of `y`. -/
theorem incidenceTrace_hasPositivePart_of_twoSlice_stationary
    (j : Fin (d + 1)) (hj : j ≠ 0) {X Y S A : Set ℝ} (E : Set Plane)
    (hX : IsOpen X) (hXc : IsPreconnected X) (hY : IsOpen Y)
    (hS : IsOpen S) (hSc : IsPreconnected S)
    (hb : D.base.1 ∈ X) (hXB : X ⊆ ball D.base.1 D.radius)
    (hQB : ∀ q ∈ Y ×ˢ S, twoParameterInsert D.base.2 j q ∈ ball D.base.2 D.radius)
    (hh : ∀ p ∈ X ×ˢ (Y ×ˢ S), scalarHeadDerivative (D.twoSliceCenters j) p ≠ 0)
    (hst : ∀ q ∈ Y ×ˢ S, ∀ x ∈ X,
      deriv (fun a => scalarGradientSlope (D.twoSliceCenters j) (a, q)) x = 0)
    (s₀ : ℝ) (hs₀ : s₀ ∈ S) (hA : MeasurableSet A) (hAY : A ⊆ Y)
    (hApos : 0 < volume A)
    (hhit : ∀ y ∈ A, ∃ s ∈ S,
      0 < volume (D.hitTimes (twoParameterInsert D.base.2 j (y, s)) E)) :
    HasPositivePart volume (D.incidenceTrace E) := by
  let ψ := D.twoSliceCenters j
  let g : Plane → ℝ := fun p => ψ (p.1, (p.2, s₀))
  let H : Plane → Plane := fun p => (p.1, g p)
  have hψ : AnalyticOnNhd ℝ ψ (X ×ˢ (Y ×ˢ S)) :=
    fun p hp => D.twoSliceCenters_analyticAt j p (hXB hp.1) (hQB p.2 hp.2)
  have hg : AnalyticOnNhd ℝ g (X ×ˢ Y) := by
    intro p hp
    exact (hψ (p.1, (p.2, s₀)) ⟨hp.1, hp.2, hs₀⟩).comp
      (f := fun p : Plane => (p.1, (p.2, s₀)))
        (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const))
  have hH : AnalyticOnNhd ℝ H (X ×ˢ Y) :=
    fun p hp => analyticAt_fst.prod (hg p hp)
  have hreg : ∀ p ∈ X ×ˢ Y, (fderiv ℝ H p).IsInvertible := by
    intro p hp
    apply triangular_fderiv_isInvertible g p (hg p hp).differentiableAt
    rw [scalar_centerChart_vertical_derivative ψ p s₀
      (hψ (p.1, (p.2, s₀)) ⟨hp.1, hp.2, hs₀⟩).differentiableAt]
    exact hh _ ⟨hp.1, hp.2, hs₀⟩
  have hXApos : 0 < volume (X ×ˢ A) := by
    change 0 < (volume.prod volume) (X ×ˢ A)
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos (hX.measure_pos volume ⟨D.base.1, hb⟩).ne' hApos.ne'
  have himage := hasPositivePart_image_of_analytic_regular H (X ×ˢ Y) (X ×ˢ A)
    hH hreg (hX.measurableSet.prod hA) (Set.prod_mono Subset.rfl hAY) hXApos
  apply himage.mono
  rintro c ⟨p, hp, rfl⟩
  obtain ⟨s, hs, hhit⟩ := hhit p.2 hp.2
  refine ⟨p.1, hXB hp.1, twoParameterInsert D.base.2 j (p.2, s),
    hQB _ ⟨hAY hp.2, hs⟩, ?_, hhit⟩
  change (p.1, D.twoSliceCenters j (p.1, (p.2, s₀))) = _
  refine Prod.ext rfl ?_
  exact (D.twoSliceCenters_independent_tail_of_stationary j hj hX hXc hY hS hSc
    hb hXB hQB hh hst p.1 hp.1 p.2 (hAY hp.2) s s₀ hs hs₀).symm

end ProjectionModel
end PlanarNikodym
