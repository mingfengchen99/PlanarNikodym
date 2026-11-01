import PlanarNikodym.Cells.SemianalyticBarrierCover
import PlanarNikodym.Cells.SemianalyticFiberCut
import PlanarNikodym.Cells.RankOneFiberCuttingStep

/-! Actual finite fiber cutting for center-critical regular strata.
Every recursive call has strictly smaller source dimension. Finite
barrier covers and regular refinements are constructed, not assumed. -/
noncomputable section
open Set Module Metric
open scoped ENNReal NNReal
namespace PlanarNikodym

theorem regular_chart_semianalytic_fiber_cut_aux {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ)) (k : ℕ) :
    ∀ Q : AnalyticStratificationChart (Fin n → ℝ), Q.dim = k →
      LocallySemianalytic Q.image → Bornology.IsBounded Q.image →
      ∀ K : Set (Fin n → ℝ), Q.image ⊆ K →
      RegularStratumEquations K Q.image Q.dim →
      (∀ q ∈ Q.source,
        finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range ≤ 1) →
      HasSemianalyticFiberCut L Q.image := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro Q hk hQ hb K hQK hreg hrQ
    by_cases hsmall : Q.dim ≤ 1
    · apply HasSemianalyticFiberCut.of_low_dimension hQ hb
      rw [Q.dimH_image]
      exact_mod_cast hsmall
    let A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (Empty → ℝ) := fun _ => 0
    obtain ⟨ι, hι, P, hcover⟩ := hQ.exists_finite_intrinsic_rank_chart_cover hb
      univ isOpen_univ (subset_univ _) A L (fun _ t => Empty.elim t)
    have hPQ (i : ι) : (P i).chart.image ⊆ Q.image := by
      intro x hx
      rw [← hcover]
      exact mem_iUnion.mpr ⟨i, hx⟩
    have hPdim (i : ι) : (P i).chart.dim ≤ Q.dim := by
      have he := dimH_mono (hPQ i)
      rw [(P i).chart.dimH_image, Q.dimH_image] at he
      exact_mod_cast he
    have hPrank (i : ι) (q : Fin (P i).chart.dim → ℝ) (hq : q ∈ (P i).chart.source) :
        finrank ℝ (L.toLinearMap.comp (fderiv ℝ (P i).chart.map q).toLinearMap).range ≤ 1 :=
      (Q.center_rank_le_of_subset_regular (P i).chart K hQK hreg (hPQ i) L hq).trans
        (hrQ _ (Q.inverse_mem_source (hPQ i (mem_image_of_mem _ hq))))
    have hPcut (i : ι) : HasSemianalyticFiberCut L (P i).chart.image := by
      by_cases hlt : (P i).chart.dim < Q.dim
      · exact ih (P i).chart.dim (by omega) (P i).chart rfl (P i).semianalytic
          (hb.subset (hPQ i)) (closure (P i).window)
          ((P i).image_window.trans subset_closure) (P i).regular (hPrank i)
      have heDim : (P i).chart.dim = Q.dim := by have hd := hPdim i; omega
      obtain ⟨rz, _, _, hr⟩ := (P i).ranks
      have hrz : rz ≤ 1 := by
        obtain ⟨q, hq⟩ := (P i).chart.connected_source.nonempty
        rw [← (hr q hq).1]
        exact hPrank i q hq
      by_cases hz : rz = 0
      · exact (P i).chart.fiber_cut_of_rank_zero L (fun q hq => (hr q hq).1.trans hz)
      have hone : rz = 1 := by omega
      have hR : ∀ q ∈ (P i).chart.source,
          finrank ℝ (L.toLinearMap.comp (fderiv ℝ (P i).chart.map q).toLinearMap).range = 1 :=
        fun q hq => (hr q hq).1.trans hone
      obtain ⟨J, hJ, R, hRP, hRcover⟩ := (P i).semianalytic.exists_finite_barrier_cover
        (hb.subset (hPQ i))
      have hRdim (j : J) : (R j).chart.dim ≤ (P i).chart.dim := by
        have hd := dimH_mono (hRP j)
        rw [(R j).chart.dimH_image, (P i).chart.dimH_image] at hd
        exact_mod_cast hd
      have hRrank (j : J) (q : Fin (R j).chart.dim → ℝ) (hq : q ∈ (R j).chart.source) :
          finrank ℝ (L.toLinearMap.comp (fderiv ℝ (R j).chart.map q).toLinearMap).range ≤ 1 :=
        ((P i).chart.center_rank_le_of_subset_regular (R j).chart (closure (P i).window)
          ((P i).image_window.trans subset_closure) (P i).regular (hRP j) L hq).trans
          (hPrank i _ ((P i).chart.inverse_mem_source (hRP j (mem_image_of_mem _ hq))))
      have hchild (j : J) : ∃ C : Set (Fin n → ℝ), C ⊆ (P i).chart.image ∧
          L '' (R j).piece ⊆ L '' C ∧ HasSemianalyticFiberCut L C := by
        by_cases hlt : (R j).chart.dim < Q.dim
        · refine ⟨(R j).chart.image, hRP j, image_mono inter_subset_left, ?_⟩
          exact ih (R j).chart.dim (by omega) (R j).chart rfl (R j).semianalytic
            (hb.subset ((hRP j).trans (hPQ i))) (closure (R j).window)
            ((R j).image_window.trans subset_closure) (R j).regular (hRrank j)
        have heR : (R j).chart.dim = (P i).chart.dim := by
          have hd := hRdim j
          omega
        have hRone : ∀ q ∈ (R j).chart.source,
            finrank ℝ (L.toLinearMap.comp (fderiv ℝ (R j).chart.map q).toLinearMap).range = 1 := by
          intro q hq
          have heT := (P i).chart.range_fderiv_eq_of_subset_regular_same_dim (R j).chart
            (closure (P i).window) ((P i).image_window.trans subset_closure)
            (P i).regular (hRP j) heR hq
          rw [LinearMap.range_comp, heT, ← LinearMap.range_comp]
          exact hR _ ((P i).chart.inverse_mem_source (hRP j (mem_image_of_mem _ hq)))
        have hpiece : LocallySemianalytic (R j).piece := (R j).semianalytic.inter
          (locallySemianalytic_coordinate_ball _ _ (R j).radius_pos)
        have hbd : Bornology.IsBounded (R j).piece := isBounded_ball.subset inter_subset_right
        obtain ⟨Z, hZR, hZ, hbZ, hdZ, heZ⟩ := (R j).chart.rank_one_fiber_cutting_step
          (R j).semianalytic (closure (R j).window) (closure_mono (R j).image_window)
          (R j).regular L (by omega) hRone (ball (R j).center (R j).radius) isOpen_ball
          hpiece hbd (closure_mono inter_subset_left |>.trans (closure_mono (R j).image_window))
          (R j).barrier (R j).analytic_barrier (R j).positive_barrier (R j).zero_boundary
        refine ⟨Z, hZR.trans (inter_subset_left.trans (hRP j)), heZ.symm.subset, ?_⟩
        obtain ⟨I, hI, T, hTcover, hTsemi, _, _, hTreg⟩ :=
          hZ.exists_finite_regular_analytic_chart_cover hbZ univ isOpen_univ (subset_univ _)
        have hTZ (a : I) : (T a).image ⊆ Z := by
          intro z hz
          rw [← hTcover]
          exact mem_iUnion.mpr ⟨a, hz⟩
        have hTcut (a : I) : HasSemianalyticFiberCut L (T a).image := by
          have htd : (T a).dim < Q.dim := by
            have hd := (dimH_mono (hTZ a)).trans hdZ
            rw [(T a).dimH_image] at hd
            have hd' : (T a).dim ≤ (R j).chart.dim - 1 := by exact_mod_cast hd
            omega
          obtain ⟨W, _, hTW, _, hnormal⟩ := hTreg a
          apply ih (T a).dim (by omega) (T a) rfl (hTsemi a) (hbZ.subset (hTZ a))
            (closure W) (hTW.trans subset_closure) hnormal
          intro q hq
          exact ((R j).chart.center_rank_le_of_subset_regular (T a) (closure (R j).window)
            ((R j).image_window.trans subset_closure) (R j).regular
            ((hTZ a).trans (hZR.trans inter_subset_left)) L hq).trans
            (hRrank j _ ((R j).chart.inverse_mem_source
              (hZR (hTZ a (mem_image_of_mem _ hq))).1))
        simpa only [hTcover] using HasSemianalyticFiberCut.finite_union
          (fun a => (T a).image) hTcut
      choose C hCP hproj hcut using hchild
      exact HasSemianalyticFiberCut.of_finite_cover_enlargements
        (fun j => (R j).piece) C hRcover hCP hproj hcut
    simpa only [hcover] using HasSemianalyticFiberCut.finite_union
      (fun i => (P i).chart.image) hPcut

theorem AnalyticStratificationChart.exists_semianalytic_fiber_cut
    {n : ℕ} (Q : AnalyticStratificationChart (Fin n → ℝ))
    (hQ : LocallySemianalytic Q.image) (hb : Bornology.IsBounded Q.image)
    (K : Set (Fin n → ℝ)) (hQK : Q.image ⊆ K)
    (hreg : RegularStratumEquations K Q.image Q.dim)
    (L : (Fin n → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (hr : ∀ q ∈ Q.source,
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range ≤ 1) :
    ∃ B : Set (Fin n → ℝ), B ⊆ Q.image ∧ LocallySemianalytic B ∧
      Bornology.IsBounded B ∧ dimH B ≤ 1 ∧ L '' B = L '' Q.image :=
  regular_chart_semianalytic_fiber_cut_aux L Q.dim Q rfl hQ hb K hQK hreg hr

end PlanarNikodym
