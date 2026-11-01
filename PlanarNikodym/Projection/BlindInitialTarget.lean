import PlanarNikodym.Projection.NonlinearBlindReplacement
import PlanarNikodym.Projection.ProjectedSweepTransfer

/-! Positive initial targets for the finite blind construction.

A transverse parameter segment has a uniformly positive projection
length for the actual centre maps. Thus the target retained during
subsequent replacements is a concrete image of a concrete compact set.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology

namespace PlanarNikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A directional derivative lower bound gives the actual endpoint gap
of a nonlinear projection of a segment. -/
theorem blind_projection_endpoint_gap
    {f : E → ℝ} {c v : E} {a m : ℝ} (ha : 0 ≤ a)
    (hf : ∀ z ∈ centeredBlindSegment c v a, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ centeredBlindSegment c v a, m ≤ fderiv ℝ f z v) :
    2 * m * a ≤ f (c + a • v) - f (c + (-a) • v) := by
  let g : ℝ → ℝ := fun t => f (c + t • v)
  have hg : ∀ t ∈ Icc (-a) a,
      HasDerivAt g (fderiv ℝ f (c + t • v) v) t := by
    intro t ht
    exact (hf _ ⟨t, ht, rfl⟩).hasFDerivAt.comp_hasDerivAt t
      (by simpa using ((hasDerivAt_id t).smul_const v).const_add c)
  have hgap := (convex_Icc (-a) a).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hg t (interior_subset ht)).deriv]; exact hd _ ⟨t, interior_subset ht, rfl⟩)
    (-a) (left_mem_Icc.mpr (by linarith)) a
    (right_mem_Icc.mpr (by linarith)) (by linarith)
  dsimp [g] at hgap
  nlinarith

/-- The projected segment has outer measure at least its uniformly
controlled endpoint gap. No image-measurability assumption is used. -/
theorem volume_blind_projection_ge
    {f : E → ℝ} {c v : E} {a m : ℝ} (ha : 0 ≤ a)
    (hf : ∀ z ∈ centeredBlindSegment c v a, DifferentiableAt ℝ f z)
    (hd : ∀ z ∈ centeredBlindSegment c v a, m ≤ fderiv ℝ f z v) :
    ENNReal.ofReal (2 * m * a) ≤ volume (f '' centeredBlindSegment c v a) := by
  have hcont : ContinuousOn (fun t : ℝ => f (c + t • v)) (Icc (-a) a) := by
    have hfc : ContinuousOn f (centeredBlindSegment c v a) :=
      fun z hz => (hf z hz).continuousAt.continuousWithinAt
    exact hfc.comp
      (show Continuous (fun t : ℝ => c + t • v) from
        continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun t ht => ⟨t, ht, rfl⟩)
  have hsubset : Icc (f (c + (-a) • v)) (f (c + a • v)) ⊆
      f '' centeredBlindSegment c v a := by
    intro y hy
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by linarith : -a ≤ a) hcont hy
    exact ⟨c + t • v, ⟨t, ht, rfl⟩, he⟩
  calc
    ENNReal.ofReal (2 * m * a) ≤
        ENNReal.ofReal (f (c + a • v) - f (c + (-a) • v)) :=
      ENNReal.ofReal_le_ofReal (blind_projection_endpoint_gap ha hf hd)
    _ = volume (Icc (f (c + (-a) • v)) (f (c + a • v))) := by
      rw [Real.volume_Icc]
    _ ≤ volume (f '' centeredBlindSegment c v a) := measure_mono hsubset

/-- A single actual compact segment supplies a positive target integral
on every positive-measure centre interval with a uniform transverse
derivative. This is an initial target, not a final null-projection set. -/
theorem lintegral_blind_projection_pos
    (ψ : ℝ → E → ℝ) {X : Set ℝ} (hX : MeasurableSet X)
    (hXpos : 0 < volume X) {c v : E} {a m : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (hf : ∀ x ∈ X, ∀ z ∈ centeredBlindSegment c v a, DifferentiableAt ℝ (ψ x) z)
    (hd : ∀ x ∈ X, ∀ z ∈ centeredBlindSegment c v a, m ≤ fderiv ℝ (ψ x) z v) :
    0 < ∫⁻ x in X, volume (ψ x '' centeredBlindSegment c v a) := by
  have hlower : ENNReal.ofReal (2 * m * a) * volume X ≤
      ∫⁻ x in X, volume (ψ x '' centeredBlindSegment c v a) := by
    calc
      ENNReal.ofReal (2 * m * a) * volume X =
          ∫⁻ _ in X, ENNReal.ofReal (2 * m * a) := by simp
      _ ≤ ∫⁻ x in X, volume (ψ x '' centeredBlindSegment c v a) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hX] with x hx
        exact volume_blind_projection_ge ha.le (hf x hx) (hd x hx)
  exact (ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) hXpos.ne').trans_le hlower

end PlanarNikodym
