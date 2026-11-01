import PlanarNikodym.Geometry.AnalyticStratificationCharts
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! A full-dimensional actual analytic immersion has ambient-open image.
This is proved by the inverse function theorem at each source point. -/
noncomputable section
open Set Filter Module
open scoped Topology
namespace PlanarNikodym

theorem AnalyticStratificationChart.derivative_surjective_of_dim_eq
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (hd : Q.dim = n) {q : Fin Q.dim → ℝ} (hq : q ∈ Q.source) :
    Function.Surjective (fderiv ℝ Q.map q) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa only [finrank_fin_fun, hd] using
    LinearMap.finrank_range_of_inj (Q.derivative_injective q hq)

theorem AnalyticStratificationChart.isOpen_image_of_dim_eq
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (hd : Q.dim = n) : IsOpen Q.image := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨q, hq, rfl⟩
  have hs := Q.derivative_surjective_of_dim_eq hd hq
  have hn := (Q.analytic_map q hq).hasStrictFDerivAt.map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr hs)
  rw [← hn]
  exact Filter.mem_map.mpr (mem_of_superset (Q.open_source.mem_nhds hq)
    (fun x hx => mem_image_of_mem Q.map hx))

end PlanarNikodym
