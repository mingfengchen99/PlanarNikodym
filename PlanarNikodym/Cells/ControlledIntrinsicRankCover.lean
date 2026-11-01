import PlanarNikodym.Cells.IntrinsicCenterRankPieces
import PlanarNikodym.Cells.FamilyCriticalCenterCover
import PlanarNikodym.Cells.CountableRankClassification

/-! The actual controlled rank cover on any bounded semianalytic source
whose closure stays inside the original analytic domain. All center-
regular strata are covered exactly, with a common compact null exception. -/
noncomputable section
open Set MeasureTheory
namespace PlanarNikodym

theorem Family.exists_controlled_rank_cover_on_semianalytic_source
    {d : ℕ} (G : Family 2 d) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (S : Set (Fin (d + 2) → ℝ)) (hS : LocallySemianalytic S)
    (hb : Bornology.IsBounded S) (hSW : closure S ⊆ (parameterFrame d) ⁻¹' G.W) :
    ∃ D : AnalyticRankCover (G.restrictTo ((parameterFrame d) '' S)),
      IsCompact D.exceptional ∧ RanDefinable D.exceptional := by
  classical
  let H := G.restrictTo ((parameterFrame d) '' S)
  have hsub : (parameterFrame d) '' S ⊆ G.W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hSW (subset_closure hx)
  have hHa : H.IsAnalytic := ha.restrictTo hsub
  obtain ⟨ι, hι, P, hcover, E, hEd, hEc, hEn, _, _, hEcrit⟩ :=
    G.exists_intrinsic_rank_cover_with_critical_exception ho ha S hS hb hSW
  have hPS (i : ι) : (P i).chart.image ⊆ S := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  let J := {i : ι // ¬ (P i).centerCritical}
  have hex (j : J) : ∃ T : Set (RankPiece H), T.Countable ∧
      (∀ R ∈ T, R.dim + 2 = (P j.val).chart.dim ∧ R.family.RanTame ∧
        R.toAnalyticPiece.image ⊆ (parameterFrame d) '' (P j.val).chart.image) ∧
      ∀ y ∈ (parameterFrame d) '' (P j.val).chart.image,
        ∃ R ∈ T, y ∈ R.toAnalyticPiece.image :=
    (P j.val).exists_countable_center_rankPiece_cover (G := H) hHa
      (image_mono (hPS j.val)) j.property
  choose T hTc _ hTcover using hex
  let pieces := ⋃ j : J, T j
  have hcount : pieces.Countable := Set.countable_iUnion hTc
  have hcov : ∀ p ∈ H.W, p.1 ∈ E ∨ ∃ R ∈ pieces, p ∈ R.toAnalyticPiece.image := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ hx)
    by_cases hi : (P i).centerCritical
    · apply Or.inl
      exact hEcrit i hi (subset_closure (mem_image_of_mem (parameterCenterDerivative d) hxi))
    · obtain ⟨R, hRT, hxR⟩ := hTcover ⟨i, hi⟩ _ (mem_image_of_mem _ hxi)
      exact Or.inr ⟨R, mem_iUnion.mpr ⟨⟨i, hi⟩, hRT⟩, hxR⟩
  let D : AnalyticRankCover H :=
    { pieces := pieces
      countable := hcount
      exceptional := E
      null_exceptional := hEn
      cover := hcov }
  exact ⟨D, hEc, hEd⟩

theorem Family.exists_controlled_rank_cover_on_coordinate_ball
    {d : ℕ} (G : Family 2 d) (ho : IsOpen G.W) (ha : G.IsAnalytic)
    (c : Fin (d + 2) → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ (parameterFrame d) ⁻¹' G.W) :
    ∃ D : AnalyticRankCover (G.restrictTo ((parameterFrame d) '' Metric.ball c r)),
      IsCompact D.exceptional ∧ RanDefinable D.exceptional :=
  G.exists_controlled_rank_cover_on_semianalytic_source ho ha (Metric.ball c r)
    (locallySemianalytic_coordinate_ball c r hr) Metric.isBounded_ball hball

end PlanarNikodym
