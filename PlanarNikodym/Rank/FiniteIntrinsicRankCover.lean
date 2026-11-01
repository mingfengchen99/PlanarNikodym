import PlanarNikodym.Rank.IntrinsicRankRefinement

/-! D-R3: genuine finite source-dimension induction. The complement of
the simultaneous regular locus lies in a semianalytic missing boundary;
all recursive charts have strictly smaller actual dimension. Overlaps
between the finitely many output charts are allowed. -/
noncomputable section
open Set Filter Submodule Module
open scoped Topology ENNReal NNReal
namespace PlanarNikodym

theorem regular_chart_finite_intrinsic_rank_cover_aux
    {n z : ℕ} {X : Type} (O : Set (Fin n → ℝ)) (hO : IsOpen O)
    (A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin z → ℝ))
    (hA : ∀ j t, AnalyticOnNhd ℝ (fun x => A x (Pi.single j 1) t) O)
    (k : ℕ) : ∀ Q : AnalyticStratificationChart (Fin n → ℝ), Q.dim = k →
      LocallySemianalytic Q.image → Bornology.IsBounded Q.image →
      ∀ V : Set (Fin n → ℝ), IsOpen V → Q.image ⊆ V → closure V ⊆ O →
      RegularStratumEquations (closure V) Q.image Q.dim →
      ∃ (ι : Type) (_ : Fintype ι) (P : ι → IntrinsicRankChart O A L),
        (⋃ i, (P i).chart.image) = Q.image := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro Q hk hQsemi hb V hV hQV hVO hnormal
    have hQclO : closure Q.image ⊆ O := (closure_mono hQV).trans hVO
    obtain ⟨h, hha, hdense, rz, rp, rc, hranks⟩ :=
      Q.exists_generic_intrinsic_ranks (closure V) (hQV.trans subset_closure) hnormal A L
        (fun j t => (hA j t).mono hVO)
    let S := {x | x ∈ Q.image ∧ h x ≠ 0}
    let T := Q.image \ S
    have hSQ : S ⊆ Q.image := fun _ hx => hx.1
    have hTQ : T ⊆ Q.image := fun _ hx => hx.1
    have hSsemi : LocallySemianalytic S :=
      hQsemi.inter_analytic_nonzero h (hha.mono (closure_mono hQV))
    have hTsemi : LocallySemianalytic T := hQsemi.inter hSsemi.compl
    have hTmissing : T ⊆ closure S \ S := fun _ hx => ⟨hdense hx.1, hx.2⟩
    obtain ⟨ιS, hιS, PS, hScov, hSsem, _, _, hSnormal⟩ :=
      hSsemi.exists_finite_regular_analytic_chart_cover (hb.subset hSQ) O hO
        ((closure_mono hSQ).trans hQclO)
    obtain ⟨ιT, hιT, PT, hTcov, hTsem, _, _, hTnormal⟩ :=
      hTsemi.exists_finite_regular_analytic_chart_cover (hb.subset hTQ) O hO
        ((closure_mono hTQ).trans hQclO)
    have hPS (i : ιS) : (PS i).image ⊆ S := by
      intro x hx
      rw [← hScov]
      exact mem_iUnion.mpr ⟨i, hx⟩
    have hPT (i : ιT) : (PT i).image ⊆ T := by
      intro x hx
      rw [← hTcov]
      exact mem_iUnion.mpr ⟨i, hx⟩
    have hPSdim (i : ιS) : (PS i).dim ≤ Q.dim := by
      have hd : ((PS i).dim : ℝ≥0∞) ≤ Q.dim := by
        rw [← (PS i).dimH_image, ← Q.dimH_image]
        exact dimH_mono ((hPS i).trans hSQ)
      exact_mod_cast hd
    have hPTdim (i : ιT) : (PT i).dim < Q.dim :=
      chart_dim_lt_of_subset_missing_boundary Q (PT i) S hSsemi hSQ
        ((hPT i).trans hTmissing)
    have hSchild (i : ιS) :
        ∃ (ι : Type) (_ : Fintype ι) (P : ι → IntrinsicRankChart O A L),
          (⋃ j, (P j).chart.image) = (PS i).image := by
      obtain ⟨U, hU, hPU, hUO, hreg⟩ := hSnormal i
      by_cases he : (PS i).dim = Q.dim
      · have hr := generic_intrinsic_ranks_on_same_dimension_subchart Q (PS i) (closure V)
          (hQV.trans subset_closure) hnormal A L h rz rp rc hranks (hPS i) he
        let R : IntrinsicRankChart O A L := ⟨PS i, hSsem i, U, hU, hPU, hUO, hreg, hr⟩
        exact ⟨Unit, inferInstance, fun _ => R, by simp only [iUnion_const]; rfl⟩
      · have hlt : (PS i).dim < Q.dim := lt_of_le_of_ne (hPSdim i) he
        exact ih (PS i).dim (by omega) (PS i) rfl (hSsem i)
          (hb.subset ((hPS i).trans hSQ)) U hU hPU hUO hreg
    have hTchild (i : ιT) :
        ∃ (ι : Type) (_ : Fintype ι) (P : ι → IntrinsicRankChart O A L),
          (⋃ j, (P j).chart.image) = (PT i).image := by
      obtain ⟨U, hU, hPU, hUO, hreg⟩ := hTnormal i
      exact ih (PT i).dim (by have hlt := hPTdim i; omega) (PT i) rfl (hTsem i)
        (hb.subset ((hPT i).trans hTQ)) U hU hPU hUO hreg
    let Qchild : ιS ⊕ ιT → AnalyticStratificationChart (Fin n → ℝ) := Sum.elim PS PT
    have hchild (i : ιS ⊕ ιT) :
        ∃ (ι : Type) (_ : Fintype ι) (P : ι → IntrinsicRankChart O A L),
          (⋃ j, (P j).chart.image) = (Qchild i).image := by
      rcases i with i | i
      · exact hSchild i
      · exact hTchild i
    choose J hJ R hR using hchild
    letI (i : ιS ⊕ ιT) : Fintype (J i) := hJ i
    refine ⟨Σ i : ιS ⊕ ιT, J i, inferInstance, (fun i => R i.1 i.2), ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨⟨i, j⟩, hxj⟩ := mem_iUnion.mp hx
      have hxi : x ∈ (Qchild i).image := by
        rw [← hR i]
        exact mem_iUnion.mpr ⟨j, hxj⟩
      rcases i with i | i
      · exact hSQ (hPS i hxi)
      · exact hTQ (hPT i hxi)
    · intro hx
      by_cases hxS : x ∈ S
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp (hScov ▸ hxS)
        have hxR : x ∈ ⋃ j, (R (Sum.inl i) j).chart.image :=
          (hR (Sum.inl i)).symm ▸ hxi
        obtain ⟨j, hxj⟩ := mem_iUnion.mp hxR
        exact mem_iUnion.mpr ⟨⟨Sum.inl i, j⟩, hxj⟩
      · have hxT : x ∈ T := ⟨hx, hxS⟩
        obtain ⟨i, hxi⟩ := mem_iUnion.mp (hTcov ▸ hxT)
        have hxR : x ∈ ⋃ j, (R (Sum.inr i) j).chart.image :=
          (hR (Sum.inr i)).symm ▸ hxi
        obtain ⟨j, hxj⟩ := mem_iUnion.mp hxR
        exact mem_iUnion.mpr ⟨⟨Sum.inr i, j⟩, hxj⟩

theorem LocallySemianalytic.exists_finite_intrinsic_rank_chart_cover
    {n z : ℕ} {X : Type} {S : Set (Fin n → ℝ)}
    (hS : LocallySemianalytic S) (hb : Bornology.IsBounded S)
    (O : Set (Fin n → ℝ)) (hO : IsOpen O) (hSO : closure S ⊆ O)
    (A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin z → ℝ))
    (hA : ∀ j t, AnalyticOnNhd ℝ (fun x => A x (Pi.single j 1) t) O) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → IntrinsicRankChart O A L),
      (⋃ i, (P i).chart.image) = S := by
  classical
  obtain ⟨ι, hι, Q, hcover, hsemi, _, _, hnormal⟩ :=
    hS.exists_finite_regular_analytic_chart_cover hb O hO hSO
  have hQS (i : ι) : (Q i).image ⊆ S := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hchild (i : ι) :
      ∃ (κ : Type) (_ : Fintype κ) (P : κ → IntrinsicRankChart O A L),
        (⋃ j, (P j).chart.image) = (Q i).image := by
    obtain ⟨V, hV, hQV, hVO, hreg⟩ := hnormal i
    exact regular_chart_finite_intrinsic_rank_cover_aux O hO A L hA (Q i).dim (Q i) rfl
      (hsemi i) (hb.subset (hQS i)) V hV hQV hVO hreg
  choose J hJ P hP using hchild
  letI (i : ι) : Fintype (J i) := hJ i
  refine ⟨Σ i : ι, J i, inferInstance, (fun i => P i.1 i.2), ?_⟩
  rw [iUnion_sigma]
  simp_rw [hP]
  exact hcover

end PlanarNikodym
