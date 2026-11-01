import PlanarNikodym.Cells.CenterOrderedStratumPieces
import PlanarNikodym.Cells.ReducedGeometry
import PlanarNikodym.Cells.IntrinsicRankCriticalCenters
import PlanarNikodym.Geometry.CoordinateIntrinsicRankTransport
import PlanarNikodym.Geometry.RegularImmersionTangent

/-! Actual constant-rank center pieces on the center-regular members of
the finite intrinsic stratification. Their tangent range and both ranks
are proved from the original stratum equations. -/
noncomputable section
open Set Filter Module
open scoped Topology
namespace PlanarNikodym

theorem IntrinsicRankChart.exists_center_rankPiece {d : ℕ} {G : Family 2 d}
    {O : Set (Fin (d + 2) → ℝ)}
    (P : IntrinsicRankChart O G.coordinateFunctionDerivative (parameterCenterDerivative d))
    (ha : G.IsAnalytic) (hPW : (parameterFrame d) '' P.chart.image ⊆ G.W)
    (hreg : ¬ P.centerCritical) {p : Fin P.chart.dim → ℝ} (hp : p ∈ P.chart.source) :
    ∃ R : RankPiece G, R.dim + 2 = P.chart.dim ∧ R.family.RanTame ∧
      R.toAnalyticPiece.image ⊆ (parameterFrame d) '' P.chart.image ∧
      parameterFrame d (P.chart.map p) ∈ R.toAnalyticPiece.image ∧
      ∀ᶠ y in 𝓝 (parameterFrame d (P.chart.map p)),
        y ∈ (parameterFrame d) '' P.chart.image → y ∈ R.toAnalyticPiece.image := by
  classical
  let e := parameterFrame d
  let Q := P.chart.postcompose e e.symm (fun x _ => e.analyticAt x)
    (fun y _ => e.symm.analyticAt y) (fun x _ => e.symm_apply_apply x)
  have hQI : Q.image = e '' P.chart.image := AnalyticStratificationChart.postcompose_image ..
  have hsurj : Function.Surjective (fderiv ℝ (fun q => (Q.map q).1) p) := by
    have hgt : 1 < finrank ℝ ((parameterCenterDerivative d).toLinearMap.comp
        (fderiv ℝ P.chart.map p).toLinearMap).range := by
      by_contra hn
      exact hreg ⟨p, hp, Nat.le_of_not_gt hn⟩
    have hD : fderiv ℝ (fun q => (Q.map q).1) p =
        (parameterCenterDerivative d).comp (fderiv ℝ P.chart.map p) := by
      exact ((parameterCenterDerivative d).hasFDerivAt.comp p
        (P.chart.analytic_map p hp).differentiableAt.hasFDerivAt).fderiv
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have hle := ((parameterCenterDerivative d).toLinearMap.comp
      (fderiv ℝ P.chart.map p).toLinearMap).range.finrank_le
    rw [finrank_fin_fun] at hle
    rw [hD, finrank_fin_fun]
    change finrank ℝ ((parameterCenterDerivative d).toLinearMap.comp
      (fderiv ℝ P.chart.map p).toLinearMap).range = 2
    omega
  obtain ⟨R, hdim, htame, hRQ, hpoint, hinj, hlocal⟩ :=
    exists_center_ordered_analytic_piece G ha Q (hQI ▸ hPW) p hp hsurj
  change R.dim + 2 = P.chart.dim at hdim
  let φ := e.symm ∘ R.embed
  have hφ : AnalyticOnNhd ℝ φ R.family.W := fun q hq =>
    (e.symm.analyticAt _).comp (R.analytic_embed q hq)
  have hφsub : φ '' R.family.W ⊆ P.chart.image := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨x, hx, he⟩ := (hQI ▸ hRQ (mem_image_of_mem _ hq))
    change e.symm (R.embed q) ∈ P.chart.image
    rw [← he, e.symm_apply_apply]
    exact hx
  have hφinj (q : Parameters 2 R.dim) (hq : q ∈ R.family.W) :
      Function.Injective (fderiv ℝ φ q) := by
    rw [fderiv_comp q e.symm.differentiableAt (R.analytic_embed q hq).differentiableAt, e.symm.fderiv]
    exact e.symm.injective.comp (hinj q hq)
  have hφdim : finrank ℝ (Parameters 2 R.dim) = P.chart.dim := by
    simpa only [Parameters, Base, Aux, finrank_prod, finrank_fin_fun, add_comm] using hdim
  obtain ⟨_, rp, rc, hr⟩ := P.ranks
  have hRanks : ConstantRanks R.family rp rc := by
    intro q hq
    have hT := P.chart.range_fderiv_eq_of_immersion_subset (closure P.window)
      (P.image_window.trans subset_closure) P.regular φ R.open_domain hφ hφsub hφdim hq (hφinj q hq)
    have hx := hφsub (mem_image_of_mem _ hq)
    have hrc := hr (P.chart.inverse (φ q)) (P.chart.inverse_mem_source hx)
    rw [P.chart.map_inverse hx] at hrc
    have hR := R.ranks_eq_coordinate_intrinsic ha hq
    change R.family.pointRank q = finrank ℝ ((G.coordinateFunctionDerivative (φ q)).domRestrict
      ((fderiv ℝ φ q).toLinearMap.range ⊓ (parameterCenterDerivative d).toLinearMap.ker)).range ∧
      R.family.curveRank q = finrank ℝ ((G.coordinateFunctionDerivative (φ q)).domRestrict
        (fderiv ℝ φ q).toLinearMap.range).range at hR
    rw [hT] at hR
    exact ⟨hR.1.trans hrc.2.1, hR.2.trans hrc.2.2⟩
  let T := R.withConstantRanks hRanks
  refine ⟨T, hdim, htame, ?_, hpoint, ?_⟩
  · exact hQI ▸ hRQ
  · change ∀ᶠ y in 𝓝 (e (P.chart.map p)), y ∈ Q.image → y ∈ R.image at hlocal
    rw [hQI] at hlocal
    exact hlocal

theorem IntrinsicRankChart.exists_countable_center_rankPiece_cover
    {d : ℕ} {G : Family 2 d} {O : Set (Fin (d + 2) → ℝ)}
    (P : IntrinsicRankChart O G.coordinateFunctionDerivative (parameterCenterDerivative d))
    (ha : G.IsAnalytic) (hPW : (parameterFrame d) '' P.chart.image ⊆ G.W)
    (hreg : ¬ P.centerCritical) :
    ∃ S : Set (RankPiece G), S.Countable ∧
      (∀ R ∈ S, R.dim + 2 = P.chart.dim ∧ R.family.RanTame ∧
        R.toAnalyticPiece.image ⊆ (parameterFrame d) '' P.chart.image) ∧
      ∀ y ∈ (parameterFrame d) '' P.chart.image, ∃ R ∈ S, y ∈ R.toAnalyticPiece.image := by
  classical
  let Z := (parameterFrame d) '' P.chart.image
  have hex (y : Z) : ∃ (R : RankPiece G) (U : Set (Parameters 2 d)),
      R.dim + 2 = P.chart.dim ∧ R.family.RanTame ∧ R.toAnalyticPiece.image ⊆ Z ∧
      IsOpen U ∧ y.val ∈ U ∧ ∀ z ∈ U, z ∈ Z → z ∈ R.toAnalyticPiece.image := by
    obtain ⟨x, hx, he⟩ := y.property
    obtain ⟨q, hq, hqx⟩ := hx
    obtain ⟨R, hd, ht, hsub, _, hloc⟩ := P.exists_center_rankPiece ha hPW hreg hq
    rw [hqx, he] at hloc
    obtain ⟨U, hUsub, hU, hyU⟩ := mem_nhds_iff.mp hloc
    exact ⟨R, U, hd, ht, hsub, hU, hyU, fun z hz => hUsub hz⟩
  choose R U hd ht hsub hU hyU hUsub using hex
  obtain ⟨T, hTc, hcov⟩ := (HereditarilyLindelofSpace.isLindelof Z).elim_countable_subcover
    U hU (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩)
  refine ⟨R '' T, hTc.image R, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact ⟨hd y, ht y, hsub y⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcov hy)
    exact ⟨R z, mem_image_of_mem _ hz, hUsub z y hyz hy⟩

end PlanarNikodym
