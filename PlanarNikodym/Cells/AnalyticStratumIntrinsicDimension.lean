import PlanarNikodym.Cells.AnalyticStratumHausdorff
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual chart dimensions equal the Hausdorff dimension of their images.
Injective derivatives give a local quantitative lower distance bound;
no dimension-independence certificate is assumed. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal NNReal Topology
namespace PlanarNikodym

theorem AnalyticStratificationChart.dimH_image {n : ℕ}
    (P : AnalyticStratificationChart (Fin n → ℝ)) : dimH P.image = P.dim := by
  apply le_antisymm P.dimH_image_le
  obtain ⟨x, hx⟩ := P.connected_source.nonempty
  have hc : ContDiffAt ℝ 1 P.map x := (P.analytic_map x hx).contDiffAt
  have hd := hc.hasStrictFDerivAt one_ne_zero
  obtain ⟨K, _, hK⟩ := (fderiv ℝ P.map x).toLinearMap.injective_iff_antilipschitz.mp
    (P.derivative_injective x hx)
  have hind : Topology.IsInducing (fderiv ℝ P.map x) :=
    (hK.isEmbedding (fderiv ℝ P.map x).continuous).isInducing
  obtain ⟨c, hcpos, hbound⟩ := (hd.isTheta_sub hind).symm.isBigO.exists_pos
  have hnear : {z : (Fin P.dim → ℝ) × (Fin P.dim → ℝ) |
      ‖z.1 - z.2‖ ≤ c * ‖P.map z.1 - P.map z.2‖} ∈ 𝓝 (x, x) := hbound.bound
  obtain ⟨V, hV, hxV, hVV⟩ := exists_nhds_square hnear
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hV.mem_nhds hxV) (P.open_source.mem_nhds hx))
  let B := ball x r
  let f : B → (Fin n → ℝ) := fun y => P.map y.val
  have hanti : AntilipschitzWith ⟨c, hcpos.le⟩ f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro y z
    have hb := hVV (show (y.val, z.val) ∈ V ×ˢ V from ⟨(hball y.property).1, (hball z.property).1⟩)
    change ‖y.val - z.val‖ ≤ c * ‖P.map y.val - P.map z.val‖ at hb
    change dist y.val z.val ≤ c * dist (P.map y.val) (P.map z.val)
    simpa only [dist_eq_norm] using hb
  have hdom : (P.dim : ℝ≥0∞) = dimH (univ : Set B) := by
    have he := isometry_subtype_coe.dimH_image (univ : Set B)
    simpa only [image_univ, Subtype.range_coe, B, Real.dimH_ball_pi_fin x hr] using he
  calc
    (P.dim : ℝ≥0∞) = dimH (univ : Set B) := hdom
    _ ≤ dimH (f '' univ) := hanti.le_dimH_image _
    _ ≤ dimH P.image := dimH_mono (by
      rintro _ ⟨y, _, rfl⟩
      exact ⟨y.val, (hball y.property).2, rfl⟩)

theorem AnalyticStratificationChart.dim_eq_of_image_eq {n : ℕ}
    (P Q : AnalyticStratificationChart (Fin n → ℝ)) (h : P.image = Q.image) :
    P.dim = Q.dim := by
  have he : (P.dim : ℝ≥0∞) = Q.dim := by rw [← P.dimH_image, ← Q.dimH_image, h]
  exact_mod_cast he

end PlanarNikodym
