import PlanarNikodym.Geometry.FiniteOpenDisjointRefinement
import PlanarNikodym.Cells.FiniteOpenRankDecomposition
import PlanarNikodym.Cells.LowDimensionalProjectionContainer
import PlanarNikodym.Cells.SemianalyticMissingBoundaryHausdorff
import PlanarNikodym.Cells.FamilyIntrinsicRankCover

/-! In zero auxiliary dimension, the frontiers introduced when making
finite open rank regions disjoint have closed null center images. This
argument deliberately uses the two-dimensional source bound. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem LocallySemianalytic.planar_open_frontier_projection_compact_null
    {U : Set (Fin 2 → ℝ)} (hU : LocallySemianalytic U) (ho : IsOpen U)
    (hb : Bornology.IsBounded U) (L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :
    IsCompact (L '' _root_.frontier U) ∧ volume (L '' _root_.frontier U) = 0 := by
  have hd : dimH (_root_.frontier U) ≤ 1 := by
    rw [_root_.frontier, ho.interior_eq]
    simpa only [Nat.cast_one] using hU.dimH_missing_boundary_le 1
      ((dimH_mono (subset_univ U)).trans_eq (Real.dimH_univ_pi_fin 2))
  have hbd : Bornology.IsBounded (_root_.frontier U) := hb.closure.subset frontier_subset_closure
  obtain ⟨hc, _, _, hn, _⟩ := hU.frontier.low_dimensional_projection_container hbd hd L
  rw [isClosed_frontier.closure_eq] at hc hn
  exact ⟨hc, hn⟩

theorem Family.exists_zero_auxiliary_rankDecomposition_of_finite_open_cover
    {N : ℕ} (G : Family 2 0) (ha : G.IsAnalytic)
    (C : Fin N → Set (Fin 2 → ℝ))
    (hCo : ∀ i, IsOpen (C i)) (hCs : ∀ i, LocallySemianalytic (C i))
    (hCb : ∀ i, Bornology.IsBounded (C i))
    (hCW : ∀ i, (parameterFrame 0) '' C i ⊆ G.W)
    (mp mc : Fin N → ℕ)
    (hr : ∀ i, ∀ x ∈ C i,
      G.pointRank (parameterFrame 0 x) = mp i ∧
      G.curveRank (parameterFrame 0 x) = mc i)
    (E : Set (Base 2)) (hEc : IsClosed E) (hEn : volume E = 0)
    (hcover : ∀ p ∈ G.W, p.1 ∈ E ∨ ∃ i, (parameterFrame 0).symm p ∈ C i) :
    Nonempty (RankDecomposition G) := by
  let L := parameterCenterDerivative 0
  have hfront (i : Fin N) :=
    (hCs i).planar_open_frontier_projection_compact_null (hCo i) (hCb i) L
  let E' := E ∪ ⋃ i, L '' frontier (C i)
  have hc : IsClosed E' := hEc.union
    (isClosed_iUnion_of_finite (fun i => (hfront i).1.isClosed))
  have hn : volume E' = 0 := measure_union_null hEn
    (measure_iUnion_null (fun i => (hfront i).2))
  apply G.exists_rankDecomposition_of_finite_open_regions ha
    (finiteOpenDisjointPatch C) (finiteOpenDisjointPatch_isOpen C hCo)
    (fun i => LocallySemianalytic.finiteOpenDisjointPatch hCs i)
    (fun i => (hCb i).subset (finiteOpenDisjointPatch_subset C i))
    (fun i => (image_mono (finiteOpenDisjointPatch_subset C i)).trans (hCW i)) mp mc
    (fun i x hx => hr i x hx.1) (finiteOpenDisjointPatch_pairwise C) E' hc hn
  intro p hp
  rcases hcover p hp with he | ⟨i, hi⟩
  · exact Or.inl (Or.inl he)
  rcases finiteOpenDisjointPatch_cover C (mem_iUnion.mpr ⟨i, hi⟩) with hf | hr
  · apply Or.inl
    apply Or.inr
    obtain ⟨j, hj⟩ := mem_iUnion.mp hf
    apply mem_iUnion.mpr
    refine ⟨j, (parameterFrame 0).symm p, hj, ?_⟩
    change (parameterFrame 0 ((parameterFrame 0).symm p)).1 = p.1
    rw [(parameterFrame 0).apply_symm_apply]
  · exact Or.inr hr

end PlanarNikodym
