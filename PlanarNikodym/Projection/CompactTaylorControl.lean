import PlanarNikodym.Core.Definitions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set Filter Metric
open scoped Topology
namespace PlanarNikodym.Wisewell

/-- Uniform first-order control with a nearby, independently chosen
linearization point. This is the Taylor remainder used in the bounded
factorial construction, where the derivative is frozen at an earlier
digit prefix than the two points being compared. -/
theorem exists_uniform_affine_remainder (f : Plane → ℝ) (R : Set Plane)
    (hR : IsCompact R) (hRc : Convex ℝ R)
    (hf : ∀ p ∈ R, DifferentiableAt ℝ f p)
    (hDf : ContinuousOn (fderiv ℝ f) R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R,
      ‖x - z‖ < δ → ‖y - z‖ < δ →
        ‖f y - f x - fderiv ℝ f z (y - x)‖ ≤ ε * ‖y - x‖ := by
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (hR.uniformContinuousOn_of_continuous hDf) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy z hz hxz hyz
  let A := fderiv ℝ f z
  let g : Plane → ℝ := fun u => f u - A u
  let S := R ∩ ball z δ
  have hS : Convex ℝ S := hRc.inter (convex_ball z δ)
  have hgd (u : Plane) (hu : u ∈ S) : HasFDerivAt g (fderiv ℝ f u - A) u :=
    (hf u hu.1).hasFDerivAt.sub A.hasFDerivAt
  have hbound (u : Plane) (hu : u ∈ S) : ‖fderiv ℝ g u‖ ≤ ε := by
    rw [(hgd u hu).fderiv]
    have h := hU u hu.1 z hz hu.2
    exact le_of_lt (by simpa only [dist_eq_norm, A] using h)
  have hxs : x ∈ S := ⟨hx, by simpa only [mem_ball, dist_eq_norm] using hxz⟩
  have hys : y ∈ S := ⟨hy, by simpa only [mem_ball, dist_eq_norm] using hyz⟩
  have h := hS.norm_image_sub_le_of_norm_fderiv_le (fun u hu => (hgd u hu).differentiableAt)
    hbound hxs hys
  convert h using 1
  congr 1
  simp only [g, map_sub]
  ring

end PlanarNikodym.Wisewell
