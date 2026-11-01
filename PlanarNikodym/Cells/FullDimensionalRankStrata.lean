import PlanarNikodym.Geometry.FullDimensionalStratum
import PlanarNikodym.Geometry.CoordinateIntrinsicRankTransport
import PlanarNikodym.Cells.RankDecomposition

/-! On a full-dimensional intrinsic-rank chart, its tangent is the entire
parameter space, so the original family's two actual ranks are constant.
The open image and the rank transfer are both proved here. -/
noncomputable section
open Set Module
namespace PlanarNikodym

theorem IntrinsicRankChart.full_dimensional_image_open
    {d : ℕ} {G : Family 2 d} {O : Set (Fin (d + 2) → ℝ)}
    (P : IntrinsicRankChart O G.coordinateFunctionDerivative (parameterCenterDerivative d))
    (hd : P.chart.dim = d + 2) :
    IsOpen ((parameterFrame d) '' P.chart.image) :=
  (parameterFrame d).toHomeomorph.isOpenMap _ (P.chart.isOpen_image_of_dim_eq hd)

theorem IntrinsicRankChart.constant_ranks_on_full_dimensional_image
    {d : ℕ} {G : Family 2 d} {O : Set (Fin (d + 2) → ℝ)}
    (P : IntrinsicRankChart O G.coordinateFunctionDerivative (parameterCenterDerivative d))
    (ha : G.IsAnalytic) (hPW : (parameterFrame d) '' P.chart.image ⊆ G.W)
    (hb : Bornology.IsBounded P.chart.image) (hd : P.chart.dim = d + 2) :
    ∃ mp mc : ℕ, ∀ y ∈ (parameterFrame d) '' P.chart.image,
      G.pointRank y = mp ∧ G.curveRank y = mc := by
  let e := parameterFrame d
  let U := e '' P.chart.image
  let R := AnalyticPiece.restrict G U (P.full_dimensional_image_open hd)
    (e.lipschitz.isBounded_image hb)
    (P.chart.connected_image.image e e.continuous.continuousOn)
    (ha.restrictTo hPW) hPW
  obtain ⟨rz, rp, rc, hr⟩ := P.ranks
  refine ⟨rp, rc, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨q, hq, hqx⟩ := hx
  subst x
  subst y
  have hT : (fderiv ℝ P.chart.map q).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr (P.chart.derivative_surjective_of_dim_eq hd hq)
  have hi := hr q hq
  rw [hT] at hi
  have hR := R.ranks_eq_coordinate_intrinsic ha
    (q := e (P.chart.map q)) (mem_image_of_mem e (mem_image_of_mem P.chart.map hq))
  have hDR : fderiv ℝ (e.symm ∘ R.embed) (e (P.chart.map q)) =
      e.symm.toContinuousLinearMap := by
    change fderiv ℝ (e.symm ∘ id) _ = _
    exact e.symm.fderiv
  dsimp only at hR
  rw [hDR] at hR
  change G.pointRank (e (P.chart.map q)) = finrank ℝ
      ((G.coordinateFunctionDerivative (e.symm (e (P.chart.map q)))).domRestrict
        (e.symm.toLinearMap.range ⊓ (parameterCenterDerivative d).toLinearMap.ker)).range ∧
    G.curveRank (e (P.chart.map q)) = finrank ℝ
      ((G.coordinateFunctionDerivative (e.symm (e (P.chart.map q)))).domRestrict
        e.symm.toLinearMap.range).range at hR
  have hTop : e.symm.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr e.symm.surjective
  rw [hTop, e.symm_apply_apply] at hR
  exact ⟨hR.1.trans hi.2.1, hR.2.trans hi.2.2⟩

end PlanarNikodym
