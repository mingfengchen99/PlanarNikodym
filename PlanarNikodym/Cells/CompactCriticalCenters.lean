import PlanarNikodym.Cells.CompactExceptionalImages
import Mathlib.MeasureTheory.Function.Jacobian

/-! Actual compact critical images in equal dimensions. Compactness is proved for
the critical locus itself before taking its image or a closure. This is not the
unequal-dimensional Morse--Sard theorem. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace PlanarNikodym

/-- The image of the actual critical subset of a compact parameter container is
closed and null. Smoothness is required only at points of that container. -/
theorem compact_critical_image_closed_null {n : ℕ}
    (f : Base n → Base n) {K : Set (Base n)} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) :
    IsClosed (f '' {x | x ∈ K ∧ (fderiv ℝ f x).det = 0}) ∧
      volume (f '' {x | x ∈ K ∧ (fderiv ℝ f x).det = 0}) = 0 := by
  let S := {x | x ∈ K ∧ (fderiv ℝ f x).det = 0}
  have hdc : ContinuousOn (fun x => (fderiv ℝ f x).det) K := by
    intro x hx
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hf x hx).continuousAt_fderiv (by norm_num))).continuousWithinAt
  have hSc : IsClosed S := hdc.preimage_isClosed_of_isClosed
    hK.isClosed isClosed_singleton
  have hSK : S ⊆ K := fun _ hx => hx.1
  have hS : IsCompact S := hK.of_isClosed_subset hSc hSK
  refine ⟨(hS.image_of_continuousOn
    (fun x hx => (hf x (hSK hx)).continuousAt.continuousWithinAt)).isClosed, ?_⟩
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (fun x hx => ((hf x hx.1).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun _ hx => hx.2)

/-- Any subset of the critical locus has image closure inside the compact null
critical image. No assertion about closures of arbitrary null sets is used. -/
theorem closure_critical_image_null_of_compact_container {n : ℕ}
    (f : Base n → Base n) {K S : Set (Base n)} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) (hSK : S ⊆ K)
    (hc : ∀ x ∈ S, (fderiv ℝ f x).det = 0) :
    volume (closure (f '' S)) = 0 := by
  obtain ⟨hclosed, hnull⟩ := compact_critical_image_closed_null f hK hf
  exact measure_mono_null (hclosed.closure_subset_iff.mpr
    (image_mono (fun x hx => ⟨hSK hx, hc x hx⟩))) hnull

/-- The analytic version keeps the actual compact critical set and its closed image. -/
theorem compact_analytic_critical_image_closed_null {n : ℕ}
    (f : Base n → Base n) {K : Set (Base n)} (hK : IsCompact K)
    (hf : AnalyticOnNhd ℝ f K) :
    IsClosed (f '' {x | x ∈ K ∧ (fderiv ℝ f x).det = 0}) ∧
      volume (f '' {x | x ∈ K ∧ (fderiv ℝ f x).det = 0}) = 0 :=
  compact_critical_image_closed_null f hK
    (fun x hx => (hf x hx).contDiffAt)

/-- Retained `AnalyticPiece`s already have full center differential: the source
contains all center coordinates and the embedding preserves them. Low-center-rank
strata must therefore be treated before conversion to this retained-piece type. -/
theorem AnalyticPiece.fderiv_center_embed {d : ℕ} {G : Family 2 d}
    (P : AnalyticPiece G) {q : Parameters 2 P.dim} (hq : q ∈ P.family.W) :
    fderiv ℝ (fun x => (P.embed x).1) q =
      ContinuousLinearMap.fst ℝ (Base 2) (Aux P.dim) := by
  have he : (fun x => (P.embed x).1) =ᶠ[𝓝 q] Prod.fst :=
    Filter.Eventually.mono (P.open_domain.mem_nhds hq)
      (fun x hx => P.keep_center x hx)
  rw [he.fderiv_eq]
  exact (ContinuousLinearMap.fst ℝ (Base 2) (Aux P.dim)).fderiv

theorem AnalyticPiece.center_embed_derivative_surjective {d : ℕ} {G : Family 2 d}
    (P : AnalyticPiece G) {q : Parameters 2 P.dim} (hq : q ∈ P.family.W) :
    Function.Surjective (fderiv ℝ (fun x => (P.embed x).1) q) := by
  rw [P.fderiv_center_embed hq]
  exact fun z => ⟨(z, 0), rfl⟩

end PlanarNikodym
