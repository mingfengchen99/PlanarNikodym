import PlanarNikodym.Rank.IntrinsicRankRegularSet
import PlanarNikodym.Cells.BoundedRegularStratumCover

noncomputable section
open Set Filter Submodule Module
open scoped Topology ENNReal NNReal
namespace PlanarNikodym

structure IntrinsicRankChart {n z : ℕ} {X : Type}
    (O : Set (Fin n → ℝ)) (A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin z → ℝ)) where
  chart : AnalyticStratificationChart (Fin n → ℝ)
  semianalytic : LocallySemianalytic chart.image
  window : Set (Fin n → ℝ)
  open_window : IsOpen window
  image_window : chart.image ⊆ window
  closure_window : closure window ⊆ O
  regular : RegularStratumEquations (closure window) chart.image chart.dim
  ranks : ChartIntrinsicRanks A L chart

theorem generic_intrinsic_ranks_on_same_dimension_subchart
    {n z : ℕ} {X : Type}
    (Q P : AnalyticStratificationChart (Fin n → ℝ)) (K : Set (Fin n → ℝ))
    (hQK : Q.image ⊆ K) (hnormal : RegularStratumEquations K Q.image Q.dim)
    (A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin z → ℝ)) (h : (Fin n → ℝ) → ℝ)
    (rz rp rc : ℕ)
    (hr : ∀ q ∈ Q.source, h (Q.map q) ≠ 0 →
      finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = rz ∧
      finrank ℝ ((A (Q.map q)).domRestrict
        ((fderiv ℝ Q.map q).toLinearMap.range ⊓ L.toLinearMap.ker)).range = rp ∧
      finrank ℝ ((A (Q.map q)).domRestrict (fderiv ℝ Q.map q).toLinearMap.range).range = rc)
    (hP : P.image ⊆ {x | x ∈ Q.image ∧ h x ≠ 0}) (hdim : P.dim = Q.dim) :
    ChartIntrinsicRanks A L P := by
  obtain ⟨c, F, hc, hFa, hF⟩ := hnormal
  refine ⟨rz, rp, rc, ?_⟩
  intro p hp
  let x := P.map p
  have hx : x ∈ Q.image ∧ h x ≠ 0 := hP (mem_image_of_mem _ hp)
  have hq := Q.inverse_mem_source hx.1
  have hrx := hr (Q.inverse x) hq (by simpa only [Q.map_inverse hx.1] using hx.2)
  rw [Q.map_inverse hx.1] at hrx
  have hQT := Q.range_fderiv_eq_ker_of_equations K hQK c F hc hFa hF (Q.inverse x) hq
  rw [Q.map_inverse hx.1] at hQT
  have hPT := P.range_fderiv_eq_ker_of_equations K (fun y hy => hQK (hP hy).1)
    c F (by rwa [hdim]) hFa (fun y hy => hF y (hP hy).1) p hp
  have heT : (fderiv ℝ P.map p).toLinearMap.range =
      (fderiv ℝ Q.map (Q.inverse x)).toLinearMap.range := hPT.trans hQT.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearMap.range_comp, heT, ← LinearMap.range_comp]
    exact hrx.1
  · rw [heT]
    exact hrx.2.1
  · rw [heT]
    exact hrx.2.2

theorem chart_dim_lt_of_subset_missing_boundary
    {n : ℕ} (Q P : AnalyticStratificationChart (Fin n → ℝ))
    (S : Set (Fin n → ℝ)) (hS : LocallySemianalytic S) (hSQ : S ⊆ Q.image)
    (hP : P.image ⊆ closure S \ S) : P.dim < Q.dim := by
  have hdimS : dimH S ≤ Q.dim := by
    rw [← Q.dimH_image]
    exact dimH_mono hSQ
  by_cases hk : Q.dim = 0
  · have hS0 : dimH S = 0 := by simpa only [hk, Nat.cast_zero, le_zero_iff] using hdimS
    obtain ⟨x, hx⟩ := P.connected_image.nonempty
    have hempty := hS.missing_boundary_eq_empty_of_dimH_zero hS0
    exact False.elim (by simpa only [hempty, mem_empty_iff_false] using hP hx)
  · have hpred : Q.dim - 1 + 1 = Q.dim := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
    have hb := hS.dimH_missing_boundary_le (Q.dim - 1) (by
      simpa only [hpred] using hdimS)
    have hdimP : P.dim ≤ Q.dim - 1 := by
      exact_mod_cast (show (P.dim : ℝ≥0∞) ≤ (Q.dim - 1 : ℕ) from
        P.dimH_image ▸ (dimH_mono hP).trans hb)
    omega

end PlanarNikodym
