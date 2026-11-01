import PlanarNikodym.Rank.SimultaneousStratumMinors
import PlanarNikodym.Rank.StackedFunctionMaps
import PlanarNikodym.Geometry.RegularStratumEquations

noncomputable section
open Set Filter Submodule Module
open scoped Topology
namespace PlanarNikodym

def ChartIntrinsicRanks {n z : ℕ} {X : Type}
    (A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin z → ℝ))
    (Q : AnalyticStratificationChart (Fin n → ℝ)) : Prop :=
  ∃ rz rp rc : ℕ, ∀ q ∈ Q.source,
    finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = rz ∧
    finrank ℝ ((A (Q.map q)).domRestrict
      ((fderiv ℝ Q.map q).toLinearMap.range ⊓ L.toLinearMap.ker)).range = rp ∧
    finrank ℝ ((A (Q.map q)).domRestrict (fderiv ℝ Q.map q).toLinearMap.range).range = rc

theorem AnalyticStratificationChart.exists_generic_intrinsic_ranks
    {n z : ℕ} {X : Type}
    (Q : AnalyticStratificationChart (Fin n → ℝ)) (K : Set (Fin n → ℝ)) (hQK : Q.image ⊆ K)
    (hnormal : RegularStratumEquations K Q.image Q.dim)
    (A : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (X → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin z → ℝ))
    (hA : ∀ j t, AnalyticOnNhd ℝ (fun x => A x (Pi.single j 1) t) K) :
    ∃ h : (Fin n → ℝ) → ℝ, AnalyticOnNhd ℝ h K ∧
      Q.image ⊆ closure {x | x ∈ Q.image ∧ h x ≠ 0} ∧
      ∃ rz rp rc : ℕ, ∀ q ∈ Q.source, h (Q.map q) ≠ 0 →
        finrank ℝ (L.toLinearMap.comp (fderiv ℝ Q.map q).toLinearMap).range = rz ∧
        finrank ℝ ((A (Q.map q)).domRestrict
          ((fderiv ℝ Q.map q).toLinearMap.range ⊓ L.toLinearMap.ker)).range = rp ∧
        finrank ℝ ((A (Q.map q)).domRestrict (fderiv ℝ Q.map q).toLinearMap.range).range = rc := by
  classical
  obtain ⟨c, F, hc, hFa, hF⟩ := hnormal
  let C (x : Fin n → ℝ) := (fderiv ℝ F x).toLinearMap
  let Y : Fin 3 → Type := ![Fin c ⊕ Fin z, Fin c ⊕ X, (Fin c ⊕ Fin z) ⊕ X]
  let B : (i : Fin 3) → (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] (Y i → ℝ) := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
    · exact fun x => stackFunctionMaps (C x) L.toLinearMap
    · exact fun x => stackFunctionMaps (C x) (A x)
    · exact fun x => stackFunctionMaps (stackFunctionMaps (C x) L.toLinearMap) (A x)
  have hC (j : Fin n) (t : Fin c) : AnalyticOnNhd ℝ (fun x => C x (Pi.single j 1) t) K := by
    intro x hx
    exact ((ContinuousLinearMap.proj t).analyticAt _).comp
      (((ContinuousLinearMap.apply ℝ (Fin c → ℝ) (Pi.single j 1)).analyticAt _).comp (hFa x hx).fderiv)
  have hBa (i : Fin 3) (j : Fin n) (t : Y i) :
      AnalyticOnNhd ℝ (fun x => B i x (Pi.single j 1) t) K := by
    fin_cases i
    · rcases t with t | t
      · exact hC j t
      · exact analyticOnNhd_const
    · rcases t with t | t
      · exact hC j t
      · exact hA j t
    · rcases t with (t | t) | t
      · exact hC j t
      · exact analyticOnNhd_const
      · exact hA j t
  obtain ⟨h, hh, hdense, r, hr⟩ := Q.simultaneous_ambient_minors K hQK Y
    (fun i j t x => B i x (Pi.single j 1) t) hBa
  refine ⟨h, hh, hdense, r 0 - c, r 2 - r 0, r 1 - c, ?_⟩
  intro q hq hqn
  let x := Q.map q
  have hx : x ∈ Q.image := mem_image_of_mem _ hq
  have hT := Q.range_fderiv_eq_ker_of_equations K hQK c F hc hFa hF q hq
  have hrB (i : Fin 3) : finrank ℝ (B i x).range = r i := by
    rw [range_eq_span_coordinates]
    exact hr x hx hqn i
  have hCrank : finrank ℝ (C x).range = c := by
    rw [LinearMap.range_eq_top.mpr (hF x hx).2, finrank_top]
    simp
  have hzrank := finrank_constrained_stack (C x) L.toLinearMap
  have hcrank := finrank_constrained_stack (C x) (A x)
  have hprank := finrank_constrained_stack (stackFunctionMaps (C x) L.toLinearMap) (A x)
  have h0 : finrank ℝ (stackFunctionMaps (C x) L.toLinearMap).range = r 0 := hrB 0
  have h1 : finrank ℝ (stackFunctionMaps (C x) (A x)).range = r 1 := hrB 1
  have h2 : finrank ℝ (stackFunctionMaps (stackFunctionMaps (C x) L.toLinearMap) (A x)).range = r 2 := hrB 2
  rw [h0, hCrank] at hzrank
  rw [h1, hCrank] at hcrank
  rw [stackFunctionMaps_ker, h2, h0] at hprank
  refine ⟨?_, ?_, ?_⟩
  · rw [range_comp_eq_map_of_range_eq _ _ _ hT]
    exact hzrank
  · rw [hT]
    exact hprank
  · rw [hT]
    exact hcrank

end PlanarNikodym
