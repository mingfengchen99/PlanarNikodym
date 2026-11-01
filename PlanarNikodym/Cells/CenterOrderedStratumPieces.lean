import PlanarNikodym.Geometry.CenterOrderedStratumLocal
import PlanarNikodym.Cells.RegularAuxiliaryCharts

/-! A full-rank centre projection on an actual analytic stratum produces
an actual tame centre-preserving subfamily of the original curve family. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace PlanarNikodym

theorem exists_center_ordered_analytic_piece {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (Q : AnalyticStratificationChart (Parameters 2 d))
    (hQW : Q.image ⊆ G.W) (p : Fin Q.dim → ℝ) (hp : p ∈ Q.source)
    (hreg : Function.Surjective (fderiv ℝ (fun u => (Q.map u).1) p)) :
    ∃ R : AnalyticPiece G,
      R.dim + 2 = Q.dim ∧ R.family.RanTame ∧ R.image ⊆ Q.image ∧
      Q.map p ∈ R.image ∧
      (∀ z ∈ R.family.W, Function.Injective (fderiv ℝ R.embed z)) ∧
      ∀ᶠ y in 𝓝 (Q.map p), y ∈ Q.image → y ∈ R.image := by
  obtain ⟨P, hdim, hclosed, hsub, hpoint, hlocal⟩ :=
    exists_center_ordered_stratum_chart Q p hp hreg
  let H : Family 2 P.aux_dim :=
    { I := G.I
      W := P.source
      γ := fun t x => G.γ t (P.map x) }
  have hclosure : closure H.W ⊆ closedBall P.center P.radius :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  have hHa : H.IsAnalyticAtClosure := by
    intro z hz
    have hball := hclosure hz.2
    have harg : AnalyticAt ℝ
        (fun w : ℝ × Parameters 2 P.aux_dim => (w.1, P.map w.2)) z :=
      analyticAt_fst.prod ((P.analytic_map z.2 hball).comp analyticAt_snd)
    exact (ha (z.1, P.map z.2) ⟨hz.1, hQW (hclosed (mem_image_of_mem _ hball))⟩).comp
      (f := fun w : ℝ × Parameters 2 P.aux_dim => (w.1, P.map w.2)) harg
  have hH : H.IsAnalytic := fun z hz => hHa z ⟨hz.1, subset_closure hz.2⟩
  let R : AnalyticPiece G :=
    { dim := P.aux_dim
      dim_le := P.dim_le
      family := H
      interval_eq := rfl
      open_domain := P.open_source
      bounded_domain := P.bounded_source
      connected_domain := P.connected_source
      analytic_family := hH
      embed := P.map
      inverse := P.inverse
      analytic_embed := P.analytic_map.mono ball_subset_closedBall
      continuous_inverse := P.continuous_inverse
      left_inv := P.left_inverse
      keep_center := P.keep_center
      maps_to := fun z hz => hQW (hsub (mem_image_of_mem _ hz))
      identity := fun _ _ _ _ => rfl }
  have hTame : H.RanTame := H.ranTame_seed_ball P.center P.radius rfl hHa
  exact ⟨R, hdim, hTame, hsub, hpoint, P.derivative_injective, hlocal⟩

/-- Compact subsets of the centre-regular locus have a genuine finite
cover by constructed tame centre-preserving analytic pieces. Images may
overlap; no disjoint global cell decomposition is asserted here. -/
theorem exists_finite_center_ordered_analytic_piece_cover {d : ℕ} (G : Family 2 d)
    (ha : G.IsAnalytic) (Q : AnalyticStratificationChart (Parameters 2 d))
    (hQW : Q.image ⊆ G.W) {K : Set (Parameters 2 d)} (hK : IsCompact K)
    (hKQ : K ⊆ Q.image)
    (hreg : ∀ y ∈ K,
      Function.Surjective (fderiv ℝ (fun u => (Q.map u).1) (Q.inverse y))) :
    ∃ s : Finset K, ∃ R : s → AnalyticPiece G,
      (∀ i, (R i).dim + 2 = Q.dim ∧ (R i).family.RanTame ∧ (R i).image ⊆ Q.image ∧
        ∀ z ∈ (R i).family.W, Function.Injective (fderiv ℝ (R i).embed z)) ∧
      K ⊆ ⋃ i, (R i).image := by
  classical
  have hlocal (y : K) : ∃ R : AnalyticPiece G,
      R.dim + 2 = Q.dim ∧ R.family.RanTame ∧ R.image ⊆ Q.image ∧
      (∀ z ∈ R.family.W, Function.Injective (fderiv ℝ R.embed z)) ∧
      ∀ᶠ w in 𝓝 y.val, w ∈ Q.image → w ∈ R.image := by
    obtain ⟨R, hd, ht, hs, _, hi, hloc⟩ := exists_center_ordered_analytic_piece G ha Q hQW
      (Q.inverse y.val) (Q.inverse_mem_source (hKQ y.property)) (hreg y.val y.property)
    rw [Q.map_inverse (hKQ y.property)] at hloc
    exact ⟨R, hd, ht, hs, hi, hloc⟩
  choose R hd ht hs hi hloc using hlocal
  have hopen (y : K) : ∃ O : Set (Parameters 2 d),
      IsOpen O ∧ y.val ∈ O ∧ ∀ w ∈ O, w ∈ Q.image → w ∈ (R y).image := by
    obtain ⟨O, hsub, hO, hyO⟩ := _root_.eventually_nhds_iff.mp (hloc y)
    exact ⟨O, hO, hyO, fun w hw => hsub w hw⟩
  choose O hO hyO hsub using hopen
  obtain ⟨s, hcov⟩ := hK.elim_finite_subcover O hO (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hyO ⟨y, hy⟩⟩)
  refine ⟨s, (fun i => R i.val), (fun i => ⟨hd i.val, ht i.val, hs i.val, hi i.val⟩), ?_⟩
  intro y hy
  obtain ⟨i, his, hyO'⟩ := mem_iUnion₂.mp (hcov hy)
  exact mem_iUnion.mpr ⟨⟨i, his⟩, hsub i y hyO' (hKQ hy)⟩

end PlanarNikodym
